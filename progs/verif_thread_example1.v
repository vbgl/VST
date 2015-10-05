Require Import floyd.proofauto.
Require Import progs.thread_example1.

Instance CompSpecs : compspecs.
Proof. make_compspecs prog. Defined.

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

Definition tlock := Tstruct _lock_t noattr.

Definition default_val_lock : reptype tlock := ([Vundef; Vundef;
Vundef; Vundef; Vundef; Vundef; Vundef; Vundef], [Vundef; Vundef;
Vundef; Vundef]).

Axiom lock_inv : share -> val -> mpred -> mpred.

Axiom lock_inv_share_join : forall sh1 sh2 sh v R, sepalg.join sh1 sh2 sh ->
  lock_inv sh1 v R * lock_inv sh2 v R = lock_inv sh v R.

Axiom lock_inv_isptr : forall sh v R, `(lock_inv sh v R) |-- !!(isptr v).

Parameter Rlock_placeholder : mpred.

Definition makelock_spec :=
  DECLARE _makelock
   WITH v : val, sh : share
   PRE [ _lock OF tptr tlock ]
     PROP (writable_share sh)
     LOCAL (temp _lock v)
     (* SEP (`(mapsto_ Tsh tlock v)) *)  (* ask andrew: that, or mapsto ... (default_val tlock) ? *)
     SEP (`(data_at_ Tsh tlock v))
   POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (`(lock_inv Tsh v Rlock_placeholder)).

Definition freelock_spec :=
  DECLARE _freelock
   WITH v : val, sh : share
   PRE [ _lock OF tptr tlock ]
     PROP (writable_share sh)
     LOCAL (temp _lock v)
     SEP (`Rlock_placeholder ; `(lock_inv sh v Rlock_placeholder))
   POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (`Rlock_placeholder ; `(mapsto_ sh tlock v)).

Definition acquire_spec :=
  DECLARE _acquire
   WITH v : val, sh : share
   PRE [ _lock OF tptr tlock ]
     PROP (readable_share sh)
     LOCAL (temp _lock v)
     SEP (`(lock_inv sh v Rlock_placeholder))
   POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (`(lock_inv sh v Rlock_placeholder) ; `Rlock_placeholder).

Definition release_spec :=
  DECLARE _release
   WITH v : val, sh : share
   PRE [ _lock OF tptr tlock ]
     PROP (readable_share sh)
     LOCAL (temp _lock v)
     SEP (`(lock_inv sh v Rlock_placeholder) ; `Rlock_placeholder)
   POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (`(lock_inv sh v Rlock_placeholder)).

Definition voidstar_funtype :=
  Tfunction
    (Tcons (tptr tvoid) Tnil)
    (tptr tvoid)
    cc_default.

Parameter spawned_precondition_placeholder : val -> mpred.

(* EVENTUALLY: add a parameter for PROP? (it's not necessary, because we can encode it in SEP) *)
(* EVENTUALLY: state an alpha-conversion theorem () and then replace EX _y .. _y with "1%positive" *)
(* EVENTUALLY: instead of LOCAL (temp _y y), make it LOCALx (temp _y y :: Q) with Q composed only on gvar s *)

Definition spawn_thread_spec := (* universe inconsistency if "WITH P" *)
  DECLARE _spawn_thread
   WITH f : val, b : val
   PRE [_f OF tptr voidstar_funtype, _args OF tptr tvoid]
     PROP ()
     LOCAL (temp _args b)
     SEP ((EX _y : ident,
     `(func_ptr'
       (WITH y : val
        PRE [ _y OF tptr tvoid ]
          PROP  ()
          LOCAL (temp _y y)
          SEP   (`(spawned_precondition_placeholder y))
        POST [tvoid]
          PROP  ()
          LOCAL ()
          SEP   (emp)
       )
       f)) ; `(spawned_precondition_placeholder b))
   POST [ tvoid ]
     PROP  ()
     LOCAL ()
     SEP   (emp).

Definition exit_thread_spec :=
  DECLARE _exit_thread
   WITH u:unit
   PRE [ ]
     PROP ()
     LOCAL ()
     SEP (emp)
   POST [ tvoid ]
     PROP  ()
     LOCAL ()
     SEP   (`FF).

Definition threads_funspecs : funspecs :=
  makelock_spec ::
  freelock_spec ::
  acquire_spec ::
  release_spec ::
  spawn_thread_spec ::
  exit_thread_spec :: nil.

Definition f_spec :=
 DECLARE _f
  WITH args_ : val, l_ : reptype tlock, sh : share
  PRE [ _args OF tptr tvoid ]
     PROP ()
     LOCAL (temp _args args_)
     SEP (`!!(readable_share sh);
          `(field_at sh (Tstruct _ab noattr) [StructField _lock] l_ args_);
          `(lock_inv sh args_ Rlock_placeholder))
  POST [ tptr tvoid ]
     EX v: val,
     PROP ()
     LOCAL (temp ret_temp nullval)
     SEP ().

Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] PROP () LOCAL () SEP ()
  POST [ tint ] PROP () LOCAL (temp ret_temp (Vint (Int.repr 4))) SEP ().

Definition Vprog : varspecs := (_f, Tfunction (Tcons (tptr tvoid) Tnil) (tptr tvoid) cc_default) :: nil.

Definition Gprog : funspecs :=
  threads_funspecs ++
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

Lemma semax_fun_id'': (* provable once we change the definition of tc_environ *)
(* I also remove the "TC &&" *)
      forall id f (* TC *)
              Espec {cs: compspecs} Delta P Q R PostCond c
            (GLBL: (var_types Delta) ! id = None),
       (glob_specs Delta) ! id = Some f ->
       (glob_types Delta) ! id = Some (type_of_funspec f) ->
       @semax cs Espec Delta 
        ((* TC &&  *)EX v : val, PROPx P (LOCALx (gvar id v :: Q)
        (SEPx (`(func_ptr' f v) :: R))))
                              c PostCond ->
       @semax cs Espec Delta ((* TC &&  *)PROPx P (LOCALx Q (SEPx R))) c PostCond.
Proof.
intros. 
apply (semax_fun_id id f Delta); auto.
eapply semax_pre_post; try apply H1; [ clear H1 | intros; entailer ].
go_lowerx.
apply exp_right with (eval_var id (type_of_funspec f) rho).
simpl.
unfold sgvar, eval_var.
unfold Map.get.
normalize.
destruct (ge_of rho id) eqn : ?.
destruct (ve_of rho id) eqn : ?.
unfold func_ptr'.
destruct p.
destruct (eqb_type (type_of_funspec f) t) _eqn : Ht.
rewrite <-(eqb_type_true _ _ Ht) in *.
hnf in H1.
Admitted.

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
  pose (lock_invariant :=
    EX n : Z,
     field_at Tsh (Tstruct _ab noattr) [StructField _a] (Vint (Int.repr n)) ab_ *
     field_at Tsh (Tstruct _ab noattr) [StructField _b] (Vint (Int.repr (2 * n))) ab_
  ).
  (* split the frame to extract the lock *)
  unfold field_at_.
  unfold_field_at 1%nat.
  fold _a _b _lock.
  fold_field_at_.
  forward_call (ab_, Tsh). (* we should give [lock_invariant] as an
  argument here but we are cheating because of the universe
  inconsistency: replace by admit "Rlock_placeholder" *)
  {
    replace Frame with [field_at_ Tsh (Tstruct _ab noattr) [StructField _a] ab_;
                        field_at_ Tsh (Tstruct _ab noattr) [StructField _b] ab_] by (unfold Frame; reflexivity).
    simpl. entailer. cancel.
    unfold data_at_, field_at_, field_at.
    normalize.
    apply andp_right.
      apply prop_right; intuition.
      now apply field_compatible_tlock; auto.
      
      apply derives_refl.
  }
  simpl.
  replace Rlock_placeholder with lock_invariant by admit.
  
  (* COMMAND: ab->a = 1; *)
  forward.
  rewrite <- field_at_offset_zero.

  (* COMMAND: ab->b = 2; *)
  forward.
  rewrite <- field_at_offset_zero.
  
  (* COMMAND: release(); *)
  forward_call (ab_, Tsh).
  {
    (* specify the passed frame evar generated by forward_call to be [ab->lock |-> l_] *)
    replace Rlock_placeholder with lock_invariant by (clear; admit).
    replace Frame with (@nil mpred) by (unfold Frame; reflexivity).
    simpl; cancel.
    unfold lock_invariant.
    apply exp_right with 1.
    cancel.
  }
  replace Rlock_placeholder with lock_invariant by admit.
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
  (* rewrite <- (@field_at_share_join CompSpecs sh1 sh2 Tsh (Tstruct _ab noattr) [StructField _lock] _ _ Join). *)
  pose (spawned_precondition := fun y : val =>
    lock_inv sh2 y lock_invariant
    (* * field_at sh2 (Tstruct _ab noattr) [StructField _lock] (force_val (sem_cast_neutral l_)) y *)
  ).
  
  forward_call (f_, ab_).
  (* in forward we might invoque a theorem saying that if we can call spawn with an equivalent (or refined) specification
     this seems too specialize, we could try to see a way around this
   *)
  {
    (* extract_trivial_liftx *)
    renormalize.
    rewrite exp_fun_comm, exp_lift_comm.
    repeat constructor.
  }
  {
    (* the second argument indeed evaluates to ab_ *)
    apply prop_right.
    destruct ab_; inversion TC; reflexivity.
  }
  {
    simpl; cancel.
    (* the argument of the global function _f is _args // eventually, an application of the alpha-conversion theorem *)
    do 2 rewrite exp_sepcon1.
    apply @exp_right with _args.
    replace spawned_precondition_placeholder with spawned_precondition in * by (clear; admit).
    match goal with [ |- _ |-- func_ptr' ?P _ * _ * _ ] => abbreviate P as fspec_spawned end.
    
    (* specify the passed frame *)
    replace Frame with [lock_inv sh2 ab_ lock_invariant] by (unfold Frame; reflexivity); subst Frame.
    (* field_at sh1 (Tstruct _ab noattr) [StructField _lock] (force_val (sem_cast_neutral l_)) ab_] : list mpred)) *)
    simpl.
    unfold spawned_precondition.
    cancel.
    
    unfold fspec, fspec_spawned, abbreviate.
    simpl.
    (* make the specifications match somehow*)
    admit.  (* theorem about equivalence of specifications *)
  }
  
  normalize.
  replace_SEP 0 (`emp).  admit. (* there is some predicate over the heap that I don't know how to handle *)
  
  (* COMMAND: aquire() *)
  assert_PROP (isptr ab_). eapply derives_trans; [ | apply lock_inv_isptr ]. entailer.
  forward_call (ab_, sh2).
  {
    replace Frame with (@nil mpred) by (unfold Frame; reflexivity).
    replace Rlock_placeholder with lock_invariant by admit.
    simpl; cancel.
  }
  replace Rlock_placeholder with lock_invariant by admit.
  
  (* COMMAND: a=ab->a *)
  normalize.
  unfold lock_invariant at 2.
  normalize; intros n.
  (* shouldn't forward succeed? *)
  match goal with [ |- semax _ (PROP  () (LOCALx ?L (SEPx ?S))) _ _] =>
  apply semax_seq with (PROP  () (LOCALx (temp _a (Vint (Int.repr n)) :: L) (SEPx S)))
  end.
  admit.
  
  (* COMMAND: while loop *)
  simpl update_tycon.
  abbreviate_semax.
  normalize.
forward_while (`lock_invariant) (`lock_invariant).

pose (Inv:=`lock_invariant).
pose (Postcond:=`emp).

  check_Delta.
  repeat (apply -> seq_assoc; abbreviate_semax).
  first [ignore (Inv: environ->mpred) 
         | fail 1 "Invariant (first argument to forward_while) must have type (environ->mpred)"].
  first [ignore (Postcond: environ->mpred)
         | fail 1 "Postcondition (second argument to forward_while) must have type (environ->mpred)"].
  apply semax_pre with Inv.
      unfold_function_derives_right .
Focus 2.
     apply semax_seq with Postcond.
      repeat match goal with
       | |- semax _ (exp _) _ _ => fail 1
       | |- semax _ (PROPx _ _) _ _ => fail 1
       | |- semax _ ?Pre _ _ => match Pre with context [ ?F ] => unfold F end
       end.
       match goal with |- semax _ ?Pre _ _ =>
          let p := fresh "Pre" in let Hp := fresh "HPre" in 
          remember Pre as p eqn:Hp;
          repeat rewrite exp_uncurry in Hp; subst p
       end.
       eapply semax_while'_new.
       
       match goal with |- semax ?Delta ?Pre (Swhile ?e _) _ =>
        first [eapply semax_while'_new | eapply semax_while'_new1]; 
        simpl typeof;
       [ reflexivity 
       | no_intros || idtac
       | do_compute_expr1 Delta Pre e; eassumption
       | no_intros || (autorewrite with ret_assert;
         let HRE := fresh "HRE" in apply derives_extract_PROP; intro HRE;
         repeat (apply derives_extract_PROP; intro); 
         do_repr_inj HRE; normalize in HRE)
       | no_intros || (let HRE := fresh "HRE" in apply semax_extract_PROP; intro HRE;
          repeat (apply semax_extract_PROP; intro); 
          do_repr_inj HRE; normalize in HRE)
        ]
       end.
       
       | simpl update_tycon 
       ]
     ]; abbreviate_semax; autorewrite with ret_assert.



  forward_while (`emp) (`emp) VAR.
  unfold lock_invariant at 2.
  normalize; intros n.
  (* shouldn't forward succeed? *)
  match goal with [ |- semax _ (PROP  () (LOCALx ?L (SEPx ?S))) _ _] =>
  apply semax_seq with (PROP  () (LOCALx (temp _a (Vint (Int.repr n)) :: L) (SEPx S)))
  end.
  admit.
  
(* these tactic and lemma are not ready for prime time *)
Ltac pull_first_SEP := match goal with |- semax _ (    PROPx ?a (LOCALx ?b (SEPx (?c :: ?d)))) _ _ =>
                             apply semax_pre with (   (PROPx  a (LOCALx  b (SEPx         d) )) * c); [entailer;cancel|] end.

Lemma semax_seqframe S CS O Delta P Q R c1 c2 RS :
  closed_wrt_modvars c1 S ->
  @semax CS O Delta P c1 (overridePost Q R) ->
  @semax CS O (update_tycon Delta c1) (Q * S) c2 (frame_ret_assert R S) ->
  frame_ret_assert R S |-- RS ->
  @semax CS O Delta (P * S) (Ssequence c1 c2) RS.
Proof.
  intros closed s1 s2 E.
  
  eapply semax_seq; [ | eapply semax_post; [ | apply s2] ].
  2: now intros ek vl; apply andp_left2, E.
  
  eapply semax_post; [ | apply semax_frame; [ auto | apply s1 ] ].
  intros ek vl x.
  unfold overridePost, frame_ret_assert; simpl.
  if_tac.
  1: now apply andp_left2; normalize.
  eapply derives_trans; [ | apply E ].
  unfold frame_ret_assert; simpl.
  now apply andp_left2, derives_refl.
Qed.

(* grab_indexes_SEP [1]. *)
(* pull_first_SEP. *)
(* eapply semax_seqframe. *)
(* unfold closed_wrt_modvars, closed_wrt_vars; intros; simpl. *)
(* (* hmmm we should be able to derive this (~="make lock does not modify other variables") from the specification of make_lock. *)
(* If we choose to use the semax axiom, we would probably need an axiom for this as well *) *)
(* admit. *)
*)
(* formulate this either as a function call or as a semax axiom *)

Lemma semax_make_lock inv {CS O Delta} P Q R _l l_ :
  (* some hypothesis about _make_lock in Delta here? *)
  @semax CS O Delta
     (PROPx P (LOCALx (temp _l l_ :: Q) (SEPx (`(is_lock Tsh l_) :: R))))
     (Scall None (Evar _make_lock (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default)) [Etempvar _l (tptr tvoid)])
     (normal_ret_assert (PROPx P (LOCALx (temp _l l_ :: Q) (SEPx (`(lock_inv Tsh l_ inv)  :: R))))).
Admitted.

idtac.

eapply semax_seq.
eapply semax_post.
Focus 2.
apply semax_make_lock.
unfold overridePost.
intros.
if_tac.
Focus 2.
unfold POSTCONDITION, abbreviate.
unfold function_body_ret_assert.
apply derives_refl.

Print exitkind.
pose (lockinv := emp).

eapply semax_post; [ | eapply (semax_make_lock lockinv) ].
intros.
unfold overridePost.
(* this makes the axiom hard to use as it is *)


evar (x : environ -> mpred).
match goal with |- semax _ (?P * _) _ _ => apply semax_seq with (P * x) end.

apply semax_frame.

apply semax_seq with (frame_ret_assert x (`emp)).

frame_SEP 0.

eapply semax_seq.
apply semax_frame.

Check semax_seq.
 
 
  (* COMMAND: make_lock(l); *)
  (* tinkering in progress *)
  eapply semax_seq'.
  let Frame := fresh "Frame" in
  evar ( Frame : (list mpred) ); eapply (semax_call_id00_wow l_ Frame);
   [ reflexivity
   | reflexivity
   | reflexivity
   | reflexivity
   | prove_local2ptree
   | repeat constructor
   | try apply local_True_right; entailer !
   | reflexivity
   | prove_local2ptree
   | repeat constructor
   | reflexivity
   | reflexivity
   | Forall_pTree_from_elements
   | Forall_pTree_from_elements
   | unfold fold_right at 1 2; cancel
   | idtac
   (*cbv beta iota; repeat rewrite exp_uncurry; try rewrite no_post_exists0;
      (first [ reflexivity | extensionality; simpl; reflexivity ]) *)
   | intros;
      try
       match goal with
       | |- extract_trivial_liftx ?A _ =>
             (has_evar A; fail 1) || (repeat constructor)
       end
   | unify_postcondition_exps
   | unfold fold_right_and; repeat rewrite and_True; auto ]
.

cbv beta iota; repeat rewrite exp_uncurry; try rewrite no_post_exists0; try reflexivity.
extensionality.
simpl.
STOP HERE

reflexivity.
      (first [ reflexivity | extensionality; simpl; reflexivity ]).


  evar (Frame : (list mpred) ); eapply (semax_call_id00_wow l_ Frame); try solve [ reflexivity | prove_local2ptree | Forall_pTree_from_elements ].
  try apply local_True_right; entailer.

  forward_call_id00_wow l_.

Ltac forward_call_id00_wow witness :=
  let Frame := fresh "Frame" in
  evar ( ?Frame : (list mpred) ); eapply (semax_call_id00_wow witness Frame);
   [ reflexivity
   | reflexivity
   | reflexivity
   | reflexivity
   | prove_local2ptree
   | repeat constructor
   | try apply local_True_right; entailer !
   | reflexivity
   | prove_local2ptree
   | repeat constructor
   | reflexivity
   | reflexivity
   | Forall_pTree_from_elements
   | Forall_pTree_from_elements
   | unfold fold_right at 1 2; cancel
   | cbv beta iota; repeat rewrite exp_uncurry; try rewrite no_post_exists0;
      (first [ reflexivity | extensionality; simpl; reflexivity ])
   | intros;
      try
       match goal with
       | |- extract_trivial_liftx ?A _ =>
             (has_evar A; fail 1) || (repeat constructor)
       end
   | unify_postcondition_exps
   | unfold fold_right_and; repeat rewrite and_True; auto ]



Ltac fwd_call' witness :=
  try
   match goal with
   | |- semax _ _ (Scall _ _ _) _ => rewrite semax_seq_skip
   end; (first
   [ revert witness;
      match goal with
      | |- let _ := ?A in _ => intro; fwd_call' A
      end
   | eapply semax_seq';
      [ first
      [ forward_call_id1_wow witness
      | forward_call_id1_x_wow witness
      | forward_call_id1_y_wow witness
      | forward_call_id01_wow witness ]
      | after_forward_call ]
   | eapply semax_seq';
      [ forward_call_id00_wow witness | after_forward_call ]
   | rewrite <- seq_assoc; fwd_call' witness ])

Print Ltac fwd_call'.
  fwd_call' l_.
  forward_call l_.
 
Admitted.



(*
Lemma JM_semax_frame_PQR:
  forall R2 Espec {cs: compspecs} Delta R1 P Q P' Q' R1' c,
     closed_wrt_modvars c (SEPx R2) ->
     @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R1))) c
                     (normal_ret_assert (PROPx P' (LOCALx Q' (SEPx R1')))) ->
     @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx (R1++R2)))) c
                     (normal_ret_assert (PROPx P' (LOCALx Q' (SEPx (R1'++R2))))).
Proof.
  intros.
  replace Q with (Q ++ []) by auto with *.
  replace Q' with (Q' ++ []) by auto with *.
  apply semax_frame_PQR; auto with *.
Qed.

Ltac JM_frame_SEP' L :=  (* this should be generalized to permit framing on LOCAL part too *)
 grab_indexes_SEP L;
 match goal with
 | |- @semax _ _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
  rewrite <- (firstn_skipn (length L) R);
    simpl length; unfold firstn, skipn;
    eapply (JM_semax_frame_PQR nil);
      [ unfold closed_wrt_modvars;  auto 50 with closed
     | ]
 | |- (PROPx _ (LOCALx _ (SEPx ?R))) |-- _ =>
  rewrite <- (firstn_skipn (length L) R);
    simpl length; unfold firstn, skipn;
    apply derives_frame_PQR
end.

  rewrite <- (firstn_skipn (length [0]) (
[`(is_lock Tsh l_); `(field_at_ Tsh (Tstruct _ab noattr) [] ab_)]
));
    simpl length; unfold firstn, skipn.
    eapply JM_semax_frame_PQR.
    (*   [ unfold closed_wrt_modvars;  auto 50 with closed *)
    (*  | ] *)
idtac
 | |- (PROPx _ (LOCALx _ (SEPx ?R))) |-- _ =>
  rewrite <- (firstn_skipn (length L) R);
    simpl length; unfold firstn, skipn;
    apply derives_frame_PQR
end.

JM_frame_SEP' [1].
*)