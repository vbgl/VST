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

Axiom is_lock : share -> val -> mpred.

Axiom lock_inv : share -> val -> mpred -> mpred.

Definition new_lock_spec :=
  DECLARE _new_lock
   WITH u : unit
   PRE [  ] PROP () LOCAL () SEP ()
   POST [ tptr tvoid ]
     EX v: val,
     PROP ()
     LOCAL (temp ret_temp v)
     SEP (`(is_lock Tsh v)).

Variable Rlock_placeholder : mpred.

Definition make_lock_spec :=
  DECLARE _make_lock
   WITH v : val
   PRE [ _lock OF tptr tvoid ]
     PROP ()
     LOCAL (temp _lock v)
     SEP (`(is_lock Tsh v))
   POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (`(lock_inv Tsh v Rlock_placeholder)).

Definition free_lock_spec :=
  DECLARE _make_lock
   WITH v : val
   PRE [ _lock OF tptr tvoid ]
     PROP ()
     LOCAL (temp _lock v)
     SEP (`Rlock_placeholder ; `(lock_inv Tsh v Rlock_placeholder))
   POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (`Rlock_placeholder ; `(is_lock Tsh v)).

Definition acquire_spec :=
  DECLARE _acquire
   WITH v : val, sh : share
   PRE [ _lock OF tptr tvoid ]
     PROP ()
     LOCAL (temp _lock v)
     SEP (`(lock_inv sh v Rlock_placeholder))
   POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (`(lock_inv sh v Rlock_placeholder) * `Rlock_placeholder).

Definition release_spec :=
  DECLARE _release
   WITH v : val, sh : share
   PRE [ _lock OF tptr tvoid ]
     PROP ()
     LOCAL (temp _lock v)
     SEP (`(lock_inv sh v Rlock_placeholder) * `Rlock_placeholder)
   POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (`(lock_inv sh v Rlock_placeholder)).

Definition voidstar_funtype :=
  Tfunction
    (Tcons (tptr tvoid) Tnil)
    (tptr tvoid)
    cc_default.

Variable spawned_precondition_placeholder : val -> mpred.

Definition spawn_thread_spec :=  (* universe inconsistency if "WITH P" *)
  DECLARE _spawn_thread
   WITH f : val, b : val
   PRE [_f OF tptr voidstar_funtype, _args OF tptr tvoid]
     PROP ()
     LOCAL (temp _args b)
     SEP ((EX _y : ident,
     `(func_ptr
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
       f)) && `(spawned_precondition_placeholder b))
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
  new_lock_spec ::
  make_lock_spec ::
  free_lock_spec ::
  acquire_spec ::
  release_spec ::
  spawn_thread_spec ::
  exit_thread_spec :: nil.

Definition f_spec :=
 DECLARE _f
  WITH args_ : val, l_ : val, sh : share
  PRE [ _args OF tptr tvoid ]
     PROP ()
     LOCAL (temp _args args_)
     SEP (`(field_at sh (Tstruct _ab noattr) [StructField _lock] l_ args_) ; `(lock_inv sh l_ Rlock_placeholder))
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
(* apply andp_right. *)
(* admit. *)
go_lowerx.
apply exp_right with (eval_var id (type_of_funspec f) rho).
simpl.
unfold sgvar, eval_var.
unfold Map.get.
normalize.
destruct (ge_of rho id) _eqn : ?.
destruct (ve_of rho id) _eqn : ?.
unfold func_ptr'.
destruct p.
destruct (eqb_type (type_of_funspec f) t) _eqn : Ht.
rewrite <-(eqb_type_true _ _ Ht) in *.
hnf in H1.
Admitted.

Ltac get_global_function'' _f :=
  eapply (semax_fun_id'' _f); try reflexivity.
  
Lemma body_main : semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  
  (* COMMAND: ab = malloc(..) *)
  (* when forward_call fails, be sure to check that the type of your
  specification matches exactly the type of the function, for example
  here I copy-pasted a specification for mallocN found in verif_queue
  that used tint instead of tuint for the regular malloc *)
  forward_call 12%Z ab_.
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
  
  (* COMMAND: l = new_lock(); *)
  forward_call tt l_.
  
  (* COMMAND: make_lock(l); *)
  pose (lock_invariant :=
    EX n : Z,
     field_at Tsh (Tstruct _ab noattr) [StructField _a] (Vint (Int.repr n)) ab_ *
     field_at Tsh (Tstruct _ab noattr) [StructField _b] (Vint (Int.repr (2 * n))) ab_
  ).
  forward_call l_ (* we should give [lock_invariant] as an argument here *).
  (* cheating because of the universe inconsistency: replace by admit "Rlock_placeholder" *)
  replace Rlock_placeholder with lock_invariant by admit.
  
  (* COMMAND: ab->lock = l; *)
  forward.
  
  (* COMMAND: ab->a = 1; *)
  forward.
  
  (* COMMAND: ab->b = 2; *)
  forward.
  
  (* COMMAND: release(l); *)
  forward_call (l_, Tsh).
  {
    (* extract_trivial_liftx *)
    renormalize.
    rewrite sepcon_lift_comm.
    repeat constructor.
  }
  {
    (* specify the passed frame evar generated by forward_call to be [ab->lock |-> l_] *)
    assert (Frame = [field_at Tsh (Tstruct _ab noattr) [StructField _lock] (force_val (sem_cast_neutral l_)) ab_])
      by (unfold Frame; reflexivity).
    replace Rlock_placeholder with lock_invariant by admit.
    (* our SEP satisfies the lock invariant *)
    simpl; cancel.
    unfold_field_at 1%nat.
    unfold _lock.
    entailer.
    cancel.
    apply exp_right with 1.
    cancel.
  }
  (* END OF COMMAND: release(l); *)
  
  (* COMMAND: spawn_thread(&f, (void* )ab); *)
  get_global_function'' _f.
  normalize.
  apply extract_exists_pre; intros f_.
  pose (spawned_precondition := fun y : val => emp (* FILL ME *)).
  forward_call (f_, ab_).
  {
    (* extract_trivial_liftx *)
    renormalize.
    rewrite exp_fun_comm.
    rewrite exp_lift_comm.
    rewrite andp_lift_comm.
    do 2 constructor.
  }
  { 
    apply prop_right.
    destruct _id0; inversion TC0; reflexivity.
  }
  {
    simpl; cancel.
    match goal with [ |- context[func_ptr' ?P _] ] => abbreviate P as SPEC end.
    (* the argument of the global function _f is _args *)
    rewrite exp_andp1.
    rewrite exp_sepcon1.
    apply @exp_right with _args.
    match goal with [ |- context[func_ptr ?P _] ] => abbreviate P as SPEC2 end.
    replace spawned_precondition_placeholder with spawned_precondition in * by (clear; admit).
    (* specify the passed frame *)
    fail.
    
    have to split the frame blablabla do that on paper
    apply andp_right.
  }
  
  compute.
simpl.

cbv zeta.

simpl.
  {
    renormalize.
    Print extract_trivial_liftx.
    Check exp_andp1.
    rewrite <-lift0C_exp.
    rewrite lift_sepcon.
    
rewrite stuff ` &&
    constructor.
    constructor.
    constructor.
  }constructor.
  

eapply semax_seq';
      [ first
      [ forward_call_id1_wow witness
      | forward_call_id1_x_wow witness
      | forward_call_id1_y_wow witness
      | forward_call_id01_wow witness ]
      | after_forward_call ]
   | eapply semax_seq';
      [ forward_call_id00_wow witness | after_forward_call ]



eapply semax_seq.
Check semax_post.

Lemma semax_post_swap R' Espec cs Delta R P c :
  @semax Espec cs Delta P c R' -> 
  (forall ek vl, local (tc_environ (exit_tycon c Delta ek)) && R' ek vl |-- R ek vl) ->
  @semax Espec cs Delta P c R.
Proof. intros; eapply semax_post; auto. Qed.

eapply semax_post_swap.

no_loads_expr e true false.
forward_setx.
  do_compute_expr Delta P Q R e v HRE.
  forward VAR.
  
  (* First, we need to get the expression that evaluates _f to compute,
  so we introduce a command: pf = &f; for debugging purposes *)
  get_global_function'' _f.
  2: simpl.
  2: reflexivity.
  reflexivity.
  get_global_function' _f.
  normalize.
  simpl eval_var.
  
  forward || forward VAR || fail.
  (* forward does not work *)
  



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