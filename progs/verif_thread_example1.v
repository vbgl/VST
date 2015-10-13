Require Import floyd.proofauto.
Require Import progs.threadlib.
Require Import progs.thread_example1.

Instance CompSpecs : compspecs.
Proof. make_compspecs prog. Defined.

Module threadlib_args <: threadlib_args.
  Let CompSpecs := CompSpecs.
  Let _lock := _lock.
  Let _lock_t := _lock_t.
  Let _f := _f.
  Let _args := _args.
  Let _makelock := _makelock.
  Let _freelock := _freelock.
  Let _acquire := _acquire.
  Let _release := _release.
  Let _spawn_thread := _spawn_thread.
  Let _exit_thread := _exit_thread.
End threadlib_args.

Module threadlib := threadlib threadlib_args.
Import threadlib.

Local Open Scope logic.

Definition natural_alignment := 8.

Definition malloc_compatible (n: Z) (p: val) : Prop :=
  match p with
  | Vptr b ofs => (natural_alignment | Int.unsigned ofs) /\
                           Int.unsigned ofs + n < Int.modulus
  | _ => False
  end.

Lemma malloc_compatible_field_compatible:
  forall (cs: compspecs) t p n,
     sizeof cenv_cs t = n ->
     legal_alignas_type t = true ->
     legal_cosu_type t = true ->
     complete_type cenv_cs t = true ->
     (alignof cenv_cs t | natural_alignment) ->
     malloc_compatible n p ->
     field_compatible t nil p.
Proof.
intros.
subst n.
destruct p; simpl in *; try contradiction.
destruct H4.
pose proof (Int.unsigned_range i).
repeat split; simpl; auto; try omega.
clear - H3 H.
eapply Zdivides_trans; eauto.
Qed.

Ltac simplify_value_fits' :=
  rewrite ?proj_sumbool_is_true by auto;
   rewrite ?proj_sumbool_is_false by auto;
   try
    match goal with
    |- context [value_fits ?sh ?t ?v] =>
        let t' := fresh "t" in
        set (t' := t); hnf in t'; subst t'; rewrite (value_fits_ind sh _ v);
        match goal with
         |- context [unfold_reptype v] =>
             change (unfold_reptype v) with v
         end; rewrite ?Z.max_r by (try computable; omega)
    end.

Definition malloc_spec :=
 DECLARE _malloc
  WITH n: Z
  PRE [ 1%positive OF tuint]
     PROP (4 <= n <= Int.max_unsigned)
     LOCAL (temp 1%positive (Vint (Int.repr n)))
     SEP ()
  POST [ tptr tvoid ]
     EX v: val,
     PROP (malloc_compatible n v)
     LOCAL (temp ret_temp v)
     SEP (`(memory_block Tsh n v)).

(* ideally the function spec would be like this, but we have to fit
   the precondition of spawn.  Fortunately, we should be able to
   relate the two through semax_body. *)
(*
Definition f_spec :=
 DECLARE _f
  WITH args_ : val, l_ : reptype tlock, sh : share
  PRE [ _args OF tptr tvoid ]
     PROP (readable_share sh)
     LOCAL (temp _args args_)
     SEP (`(field_at sh (Tstruct _ab noattr) [StructField _lock] l_ args_);  (* obsolete? *)
          `(lock_inv sh args_ Rlock_placeholder))
  POST [ tptr tvoid ]
     PROP ()
     LOCAL ()
     SEP ().
*)

Definition lock_resource p :=
  EX n : Z,
     field_at Tsh (Tstruct _ab noattr) [StructField _a] (Vint (Int.repr n)) p *
     field_at Tsh (Tstruct _ab noattr) [StructField _b] (Vint (Int.repr (2 * n))) p.

Definition f_spec :=
 DECLARE _f
  WITH args_ : val
  PRE [ _args OF tptr tvoid ]
     PROP ()
     LOCAL (temp _args args_)
     SEP (`(EX sh : share, !!(readable_share sh) && lock_inv sh args_ (lock_resource args_)))
  POST [ tptr tvoid ]
     PROP ()
     LOCAL ()
     SEP ().

Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] PROP () LOCAL () SEP ()
  POST [ tint ] PROP () LOCAL (temp ret_temp (Vint (Int.repr 4))) SEP ().

Definition Vprog : varspecs := (_f, Tfunction (Tcons (tptr tvoid) Tnil) (tptr tvoid) cc_default) :: nil.

Definition Gprog : funspecs :=
  malloc_spec :: f_spec :: main_spec::nil.

Lemma sepcon_lift_comm A B : `A * `B = `(A * B).
Proof.
  apply pred_ext; entailer.
Qed.

Lemma exp_fun_comm A B P : (fun b : B => (EX a : A, (P a b))) = exp P.
Proof.
  extensionality b.
  apply pred_ext; entailer.
  unfold exp; simpl.
  apply exp_right with a; auto.
Qed.

Lemma exp_lift_comm A P : (EX x : A, `(P x)) = `(EX x : A, P x).
Proof.
  apply pred_ext; entailer; eapply exp_right; eauto.
Qed.

Lemma andp_lift_comm A B : `A && `B = `(A && B).
Proof.
  apply pred_ext; entailer.
Qed.

Lemma split_readable_share sh :
  readable_share sh ->
  exists sh1, exists sh2,
    readable_share sh1 /\
    readable_share sh2 /\
    sepalg.join sh1 sh2 sh.
Admitted.

Lemma split_Tsh :
  exists sh1, exists sh2,
    readable_share sh1 /\
    readable_share sh2 /\
    sepalg.join sh1 sh2 Tsh.
Proof.
  apply split_readable_share; auto.
Qed.

Lemma semax_fun_id'' id f Espec {cs} Delta P Q R Post c :
  (var_types Delta) ! id = None ->
  (glob_specs Delta) ! id = Some f ->
  (glob_types Delta) ! id = Some (type_of_funspec f) ->
  @semax cs Espec Delta
    (EX v : val, PROPx P
      (LOCALx (gvar id v :: Q)
      (SEPx (`(func_ptr' f v) :: R)))) c Post ->
  @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R))) c Post.
Proof.
intros V G GS SA.
apply (semax_fun_id id f Delta); auto.
eapply semax_pre_post; try apply SA; [ clear SA | intros; entailer ].
go_lowerx.
apply exp_right with (eval_var id (type_of_funspec f) rho).
entailer.
apply andp_right.
- (* about gvar *)
  apply prop_right.
  unfold gvar, eval_var, Map.get.
  destruct H as (_ & _ & DG & DS).
  destruct (DS id _ GS) as [-> | (t & E)]; [ | congruence].
  destruct (DG id _ GS) as (? & -> & ?); auto.

- (* about func_ptr/func_ptr' *)
  unfold func_ptr'.
  rewrite <- andp_left_corable, andp_comm; auto.
  apply corable_func_ptr.
Qed.

Ltac get_global_function'' _f :=
  eapply (semax_fun_id'' _f); try reflexivity.

Ltac fold_field_at_' a :=
  try match a with
    | PROPx _ ?a => fold_field_at_' a
    | LOCALx _ ?a => fold_field_at_' a
    | SEPx ?l => fold_field_at_' l
    | `?h :: ?t => fold_field_at_' h; fold_field_at_' t
    | ?a * ?b => fold_field_at_' b; fold_field_at_' a
    | ?a && ?b => fold_field_at_' a; fold_field_at_' b
    | @mapsto ?cs ?sh ?ty ?val ?p => try replace (@mapsto cs sh ty val p) with (@mapsto_ cs sh ty p) by reflexivity
    | @data_at ?cs ?sh ?ty ?val ?p => try replace (@data_at cs sh ty val p) with (@data_at_ cs sh ty p) by reflexivity
    | @field_at ?cs ?sh ?ty ?path ?val ?p => try replace (@field_at cs sh ty path val p) with (@field_at_ cs sh ty path p) by reflexivity
    | nil => idtac
  end.

Ltac fold_field_at_ :=
  match goal with
    | |- semax _ ?a _ _ => fold_field_at_' a
    | |- ?a |-- ?b => fold_field_at_' a; fold_field_at_' b
  end.

Lemma field_compatible_tlock v :
  field_compatible (Tstruct _ab noattr) [StructField _lock] v ->
  field_compatible tlock [] v.
Proof.
  destruct v; unfold field_compatible; intuition.
  unfold size_compatible, sizeof in *; simpl in *.
  omega.
Qed.

Lemma body_main : semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  
  (* COMMAND: ab = malloc(..) *)
  (* when forward_call fails, be sure to check that the type of your
  specification matches exactly the type of the function, for example
  here I copy-pasted a specification for mallocN found in verif_queue
  that used tint instead of tuint for the regular malloc *)
  forward_call 32%Z ab_.
  now match goal with [|-_<=_<=_] => compute; intuition; congruence end.
  
  (* transforming memory_block into field_at_ *)
  replace_SEP 0 (`(field_at_ Tsh  (Tstruct _ab noattr) [] ab_)).
  { entailer. rewrite field_at__memory_block. simpl. unfold field_address. simpl.
    if_tac; [ now entailer | ].
    exfalso; apply H0.
    unfold field_compatible.
    intuition; simpl; try reflexivity; destruct _id; simpl; auto; unfold malloc_compatible in *; intuition.
    unfold natural_alignment, align_attr in *; simpl in *.
    match goal with [ H : ( _ | _ ) |- _ ] => destruct H as [x Ex] end.
    exists (2 * x)%Z; omega. }
  
  (* COMMAND: makelock(); *)
  (* establish the lock invariant *)
  (* split the frame to extract the lock *)
  unfold field_at_.
  unfold_field_at 1%nat.
  fold _a _b _lock.
  fold_field_at_.
  forward_call_threadlib (ab_, Tsh) (lock_resource ab_).
  {
    replace Frame with [field_at_ Tsh (Tstruct _ab noattr) [StructField _a] ab_;
                        field_at_ Tsh (Tstruct _ab noattr) [StructField _b] ab_] by (unfold Frame; reflexivity).
    simpl. entailer. cancel.
    unfold data_at_, field_at_, field_at.
    normalize.
    apply andp_right.
      apply prop_right; intuition.
        now apply field_compatible_tlock; auto.
        now apply default_value_fits.
      
      now apply derives_refl.
  }
  simpl.
  
  (* COMMAND: ab->a = 1; *)
  forward.
  rewrite <- field_at_offset_zero.

  (* COMMAND: ab->b = 2; *)
  forward.
  rewrite <- field_at_offset_zero.
  
  (* COMMAND: release(); *)
  forward_call_threadlib (ab_, Tsh) (lock_resource ab_).
  {
    (* specify the passed frame evar generated by forward_call to be [ab->lock |-> l_] *)
    replace Frame with (@nil mpred) by (unfold Frame; reflexivity).
    simpl; cancel.
    unfold lock_resource.
    apply exp_right with 1.
    cancel.
  }
  (* END OF COMMAND: release(); *)
  
  (* COMMAND: spawn_thread(&f, (void* )ab); *)
  
  (* get function specification *)
  get_global_function'' _f.
  normalize.
  apply extract_exists_pre; intros f_.
  match goal with [ |- context[func_ptr' ?P _] ] => abbreviate P as fspec end.
  
  (* build the spawned frame *)
  destruct split_Tsh as (sh1 & sh2 & Rsh1 & Rsh2 & Join).
  rewrite <- (lock_inv_share_join _ _ _ _ _ Join).
  pose (spawned_precondition := fun y : val =>
    EX sh : share, !!readable_share sh && lock_inv sh y (lock_resource y)).
  
  normalize.
  forward_call_threadlib (f_, ab_) spawned_precondition.
  (* in forward we might invoque a theorem saying that if we can call
     spawn with an equivalent (or refined) specification this seems
     too specialize, we could try to see a way around this *)
  {
    (* extract_trivial_liftx *)
    (* renormalize. *)
    rewrite (* exp_fun_comm, *) exp_lift_comm.
    repeat constructor.
  }
  {
    (* the second argument indeed evaluates to ab_ *)
    apply prop_right.
    destruct _id; inversion TC; reflexivity.
  }
  {
    simpl; cancel.
    (* the argument of the global function _f is _args // eventually, an application of the alpha-conversion theorem *)
    do 2 rewrite exp_sepcon1.
    apply @exp_right with _args.
    match goal with [ |- _ |-- func_ptr' ?P _ * _ * _ ] => abbreviate P as fspec_spawned end.
    
    (* specify the frame that stays *)
    replace Frame with [lock_inv sh1 ab_ (lock_resource ab_)] by (unfold Frame; reflexivity); subst Frame.
    (* field_at sh1 (Tstruct _ab noattr) [StructField _lock] (force_val (sem_cast_neutral l_)) ab_] : list mpred)) *)
    simpl.
    unfold spawned_precondition.
    cancel.
    apply exp_right with sh2; entailer.
  }
  
  normalize.
  replace_SEP 0 (`emp).  admit. (* there is some predicate over the heap that I don't know how to handle *)
  
  (* COMMAND: aquire() *)
  assert_PROP (isptr ab_). eapply derives_trans; [ | apply lock_inv_isptr ]. entailer.
  forward_call_threadlib (ab_, sh1) (lock_resource ab_).
  
  (* COMMAND: a=ab->a *)
  normalize.
  unfold lock_resource at 2.
  normalize; intros n.
  flatten_sepcon_in_SEP.
  forward.
  
  (* COMMAND: while loop *)
  drop_LOCAL 1%nat.
  pose (loop_inv := @exp (environ -> mpred) _ _ (fun n : Z =>
    PROP ()
    LOCAL (temp _a (Vint (Int.repr n)); temp _ab__1 ab_)
    SEP (
      `(field_at Tsh (Tstruct _ab noattr) [StructField _a] (Vint (Int.repr n)) ab_) ;
      `(field_at Tsh (Tstruct _ab noattr) [StructField _b] (Vint (Int.repr (2 * n))) ab_) ;
      `(lock_inv sh1 ab_ (lock_resource ab_))
    )
  )).
  forward_while loop_inv a_.
  now apply exp_right with n; entailer (* precondition => loop invariant *).
  now apply prop_right, I (* loop condition is well-behaved *).
  {
    (* loop body *)
    
    (* COMMAND: release() *)
    forward_call_threadlib (ab_, sh1) (lock_resource ab_).
    {
      replace Frame with (@nil mpred) by (unfold Frame; reflexivity).
      simpl fold_right.
      unfold lock_resource.
      cancel.
      apply exp_right with a_.
      cancel.
    }
    
    (* COMMAND: acquire() *)
    forward_call_threadlib (ab_, sh1) (lock_resource ab_).
    
    (* COMMAND: a = ab->a; *)
    unfold lock_resource at 2.
    clear n; normalize; intros n.
    flatten_sepcon_in_SEP.
    forward.
    
    (* back to loop invariant *)
    apply exp_right with n.
    entailer.
  }
  (* after the loop *)
  
  (* COMMAND: b = ab->b; *)
  forward.
  
  (* COMMAND: freelock(&ab->lock); *)
  forward_call_threadlib (ab_, Tsh) (lock_resource ab_).
  {
    replace Frame with (@nil mpred) by (unfold Frame; reflexivity).
    simpl fold_right.
    unfold lock_resource at 2.
    normalize.
    apply exp_right with a_.
    cancel.
    (* HERE we cannot free the lock because we need total ownership.
    To solve this, we must add "lock_inv sh2" to the lock invariant *)
    admit.
  }
  normalize.
  
  (* COMMAND: return(b); *)
  forward.
Qed.

Lemma body_f : semax_body Vprog Gprog f_f f_spec.
Proof.
  start_function.
  normalize; intros sh.
  normalize.
  forward.
  assert_PROP (isptr args_). eapply derives_trans; [ | apply lock_inv_isptr ]; entailer.
  forward_call_threadlib (args_, sh) (lock_resource args_).
  {
    destruct _id0; inversion H0; simpl.
    rewrite int_add_repr_0_r; entailer.
  }
  normalize.
  
  unfold lock_resource at 2.
  normalize; intros n.
  normalize.
  forward.
  
  forward.
  
  forward.
  
  forward.
  
  forward_call_threadlib (args_, sh) (lock_resource args_).
  {
    replace Frame with (@nil mpred) by (unfold Frame; reflexivity).
    unfold lock_resource.
    simpl; cancel.
    apply exp_right with (n + 1).
    cancel.
    apply derives_refl'; repeat f_equal.
    destruct n; simpl; auto.
  }
  
  forward_call_threadlib tt tt.
  {
    replace Frame with (@nil mpred) by (unfold Frame; reflexivity).
    (* ??? *)
    admit.
  }
  
  forward.
Qed.
