Require Import floyd.proofauto.
Require Import progs.threadlib.
Load threaded_counter.

Local Open Scope logic.

Instance CompSpecs : compspecs.
Proof. make_compspecs prog. Defined.

Module threadlib_args <: threadlib_args.
  Let CompSpecs := CompSpecs.
  Let _lock := _ctr_lock.
  Let _lock_t := _lock_t.
  Let _f := _thread_func.
  Let _args := _ctr_context__1.
  Let _makelock := _makelock.
  Let _freelock := 100%positive. (*Not used yet*)
  Let _acquire := _acquire.
  Let _release := _release.
  Let _spawn_thread := _spawn_thread.
  Let _exit_thread := 101%positive. (*Not used yet*)
End threadlib_args.

Module threadlib := threadlib threadlib_args.
Import threadlib.

Definition t_struct_mutex1 := Tstruct _ctr_lock noattr.


(**************************************************)
(*                 Specifications                 *)
(**************************************************)

(* Sequential counter specifications*)

Definition reset_spec :=
 DECLARE _reset
  WITH  ctr: val, sh: share
  PRE  [_ctr OF tptr tint] 
        PROP (writable_share sh)
        LOCAL(temp _ctr ctr)
        SEP(`(data_at_ sh tint ctr))
  POST [tvoid]
        PROP()
        LOCAL()
        SEP( `(data_at sh tint (repinj tint Int.zero) ctr)).

Definition read_spec :=
 DECLARE _read
  WITH z : int, ctr: val, sh: share
  PRE  [_ctr OF tptr tint] 
        PROP (readable_share sh)
        LOCAL(temp _ctr ctr)
        SEP(`(data_at sh tint (repinj tint z) ctr))
  POST [tint]
        PROP()
        LOCAL( temp ret_temp (Vint z))
        SEP(`(data_at sh tint (repinj tint z) ctr)).

Definition incr_spec :=
 DECLARE _incr
  WITH z : int, ctr: val, sh: share
  PRE  [_ctr OF tptr tint] 
        PROP (writable_share sh)
        LOCAL(temp _ctr ctr)
        SEP(`(data_at sh tint (repinj tint z) ctr))
  POST [tvoid]
        PROP()
        LOCAL()
        SEP(`(data_at sh tint (repinj tint (Int.add z Int.one)) ctr)).

Definition counter_funspecs : funspecs :=
  reset_spec ::
(*  freelock_spec :: *)
  incr_spec ::
  read_spec ::
  (*  exit_thread_spec ::*)
  nil.

(* Threaded program specifications*)

Definition counter_invariant field_ctr:=
  EX z : int,
  EX ctr : val,
     (data_at Tsh tint (repinj tint z) ctr)*
     (field_at Tsh (Tstruct _ctr_context noattr) [StructField _ctr] ctr field_ctr).
Definition thread_invariant field_ctr sh_ctr:=
  (lock_inv sh_ctr (offset_val (Int.repr 32) field_ctr) (counter_invariant field_ctr)).

Definition thread_func_spec :=
  DECLARE _thread_func
  WITH  context_:val
   PRE [_context OF tptr tvoid]
     PROP () (*Holds partial ownerchip of two locks*)
     LOCAL (temp _context context_)
     SEP ( `(EX sh_thr: share,
             EX sh_ctr: share,
                        lock_inv sh_thr context_ (thread_invariant context_ sh_ctr) &&
                                 !!readable_share sh_thr *
                        lock_inv sh_ctr (offset_val (Int.repr 32) context_) (counter_invariant context_) &&
                                 !!readable_share sh_ctr))
   POST [tptr tvoid ]
     PROP ()
     LOCAL ()
     SEP (`(EX sh_thr: share,
            EX sh_ctr: share,
                        lock_inv sh_thr context_ (thread_invariant context_ sh_ctr) &&
                                 !!readable_share sh_thr)).

Definition main_spec :=
 DECLARE _main
  WITH tt:unit
  PRE  [] 
        PROP ()
        LOCAL()
        SEP()
  POST [tint]
  EX z:int, EX ctr:val,
        PROP()
        LOCAL( temp ret_temp (Vint z)) (* Should be (Int.repr 2)*)
        SEP(  `(data_at Tsh tint (repinj tint z) ctr)).



Definition natural_alignment := 8.

Definition malloc_compatible (n: Z) (p: val) : Prop :=
  match p with
  | Vptr b ofs => (natural_alignment | Int.unsigned ofs) /\
                           Int.unsigned ofs + n < Int.modulus
  | _ => False
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

Definition Vprog : varspecs := (_ctr_lock, tlock)::(_ctr, tptr tint)::nil.

Definition Gprog : funspecs :=
  counter_funspecs ++ malloc_spec :: thread_func_spec::main_spec::nil.


(**************************************************)
(*                   Verification                 *)
(**************************************************)

(*Verification of the sequential counter functions*)

Lemma body_incr:  semax_body Vprog Gprog f_incr incr_spec.
Proof.
 start_function.

 (*COMMAND: int t = *ctr;*)
 forward.

 (*COMMAND *ctr = t + 1; *)
 forward.

 (*END*)
 forward.
Qed.

Lemma body_reset:  semax_body Vprog Gprog f_reset reset_spec.
Proof.
 start_function.

 (* ctr = 0;*)
 forward.
 (*End*)
 forward.
Qed.


Lemma body_read:  semax_body Vprog Gprog f_read read_spec.
Proof.
  start_function.
  (*int* ctr0 = ctr;*)
  forward.
  (*int t = *ctr0;*)
  forward.
  (*return t;*)
  forward. 
Qed.


Lemma body_thread_func_spec:semax_body Vprog Gprog f_thread_func thread_func_spec.
Proof.
  start_function.
  normalize. intro sh_thr.
  normalize. intro sh_ctr.
  normalize.

  (*COMMAND: struct ctr_context *ctr_context = (struct ctr_context * )context;*)
  Axiom lock_inv_isptr : forall sh v R, lock_inv sh v R |-- !!(isptr v).
  assert_PROP (isptr context_). entailer.
  rewrite (add_andp _ _ (lock_inv_isptr _ _ _)).
  normalize.
  forward.
  
  (*COMMAN: thread_lock_ptr = ctr_context->thread_lock;*)
  forward. 

  (*COMMAN: ctr_lock_ptr = &ctr_context->ctr_lock*)
  forward.

  (*CALL: acquire*)
  forward_call_threadlib ((offset_val (Int.repr 32) context_), sh_ctr)
                         (counter_invariant context_).
(*  forward_call  ((offset_val (Int.repr 32) context_), sh_ctr). *)
  
  (*COMMAN: int *ctr = ctr_context->ctr; *)
  unfold counter_invariant at 2.
  normalize. intros z.
  normalize. intros ctr.
  normalize. 
  forward.

  (*CALL: incr*)
  rewrite (field_at_data_at _ _ [StructField _ctr]).
  (*assert (writable_share Tsh) by auto.*)
  forward_call (z, ctr, Tsh).
  rewrite <- (field_at_data_at _ _ [StructField _ctr]).

  (*Fold the invariant*)
  eapply (semax_pre0 (
              (PROP  ()
      LOCAL  (temp _ctr ctr;
      temp _ctr_lock_ptr (offset_val (Int.repr 32) context_);
      temp _thread_lock_ptr context_; temp _ctr_context__1 context_;
      temp _context context_)
      SEP  (`(lock_inv sh_ctr (offset_val (Int.repr 32) context_)
           (counter_invariant context_)); `(counter_invariant context_);
                     `(lock_inv sh_thr context_ (thread_invariant context_ sh_ctr)))))).
  { entailer. cancel.
  unfold counter_invariant; normalize.
  eapply (exp_right (Int.add z Int.one)). normalize.
  eapply (exp_right (eval_id _ctr rho)). normalize.
  }
  
  (*CALL: release ctr*)
  forward_call_threadlib ((offset_val (Int.repr 32) context_), sh_ctr)
                         (counter_invariant context_).
  (*forward_call ((offset_val (Int.repr 32) context_), sh_ctr).*)
  
  (*call release*)
  forward_call_threadlib (context_, sh_thr)
                         (thread_invariant context_ sh_ctr).
  unfold thread_invariant.
  
  forward.
  eapply (exp_right sh_thr).
  entailer.
  unfold thread_invariant.
  eapply (exp_right sh_ctr). entailer.
Qed.



Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.

  (*call malloc (context)*)
  forward_call 68%Z ctr_context_.
  compute; intuition; congruence.
  
  replace_SEP 0 (`(field_at_ Tsh  (Tstruct _ctr_context noattr) [] ctr_context_)).
  { entailer. rewrite field_at__memory_block. simpl. unfold field_address. simpl.
    if_tac; [ now entailer | ].
    exfalso; apply H0.
    unfold field_compatible.
    intuition; simpl; try reflexivity; destruct _id; simpl; auto; unfold malloc_compatible in *; intuition.
    unfold natural_alignment, align_attr in *; simpl in *.
    match goal with [ H : ( _ | _ ) |- _ ] => destruct H as [x Ex] end.
    exists (2 * x)%Z; omega. }

  (*COMMAND: lock_t *thread_lock_ptr = &ctr_context->thread_lock;*)
  forward.
  
  (*COMMAND: lock_t *ctr_lock_ptr = &ctr_context->ctr_lock;*)
  forward.
  
  (*call malloc (context)*)
  forward_call 4%Z ctr_.
  compute; intuition; congruence.

  replace_SEP 0 (`(field_at_ Tsh tint [] ctr_)).
  { entailer. rewrite field_at__memory_block. simpl. unfold field_address. simpl.
    if_tac; [ now entailer | ].
    exfalso; apply H1.
    unfold field_compatible.
    intuition; simpl; try reflexivity; destruct _id; simpl; auto; unfold malloc_compatible in *; intuition.
    unfold natural_alignment, align_attr in *; simpl in *.
    match goal with [ H : ( _ | _ ) |- _ ] => destruct H as [x Ex] end.
    exists (2 * x)%Z; omega. }
  
  (*COMMAND: ctr_context->ctr = ctr; *)
  forward. rewrite <- field_at_offset_zero.

  (*call reset*)
  change (field_at_ Tsh tint [] ctr_) with ((data_at Tsh tint Vundef ctr_)).
  forward_call (ctr_, Tsh).
  
  (*call makelock(ctr_lock_ptr);*)
  assert (Wsh: writable_share Tsh) by apply semax_call.writable_share_top.
  unfold_field_at 1%nat.
  normalize.
  rewrite (field_at_compatible' _ _ [StructField 11%positive]).
  normalize.
  rewrite (field_at_data_at _ _ [StructField 11%positive]).
  replace (field_address (Tstruct _ctr_context noattr)
                         [StructField 11%positive] ctr_context_) with
  (offset_val (Int.repr 32) ctr_context_) by (unfold field_address; if_tac; tauto).
  forward_call_threadlib ((offset_val (Int.repr 32) ctr_context_) , Tsh)
                         (counter_invariant ctr_context_).
  (*forward_call ((offset_val (Int.repr 32) ctr_context_) , Tsh).*) 

  (*call release(&ctr_lock)*)
  forward_call_threadlib ((offset_val (Int.repr 32) ctr_context_) , Tsh)
                         (counter_invariant ctr_context_).
 (* forward_call ((offset_val (Int.repr 32) ctr_context_) , Tsh).*)

  unfold counter_invariant.
  normalize. apply exp_right with (Int.repr 0).
  normalize. apply exp_right with ctr_.
  fold Int.zero.  fold _ctr.
  rewrite data_at_isptr at 1.
  normalize.
  cancel.
  (*TO USE: sem_cast_neutral_ptr*)
  
  (*call makelock(&thread_lock_ptr)*)
  rewrite (field_at_compatible' _ _ [StructField 10%positive]).
  normalize.
  rewrite (field_at_data_at _ _ [StructField 10%positive]).
  replace (field_address (Tstruct _ctr_context noattr)
                         [StructField 10%positive] ctr_context_) with
  (offset_val (Int.repr 0) ctr_context_ ) by (unfold field_address; if_tac;  tauto).
  replace (offset_val (Int.repr 0) ctr_context_ ) with (ctr_context_) by admit.
  
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
  destruct split_Tsh as (sh_ctr1 & sh_ctr2 & Rsh_ctr1 & Rsh_ctr2 & Join_ctr).
  rewrite <- (lock_inv_share_join _ _ _ _ _ Join_ctr).
  forward_call_threadlib (ctr_context_ , Tsh)
                         (thread_invariant ctr_context_ sh_ctr1).
  (*forward_call (ctr_context_ , Tsh). *)
  
  (*CALL: spawn*)

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
  
  get_global_function'' _thread_func.
  normalize.
  apply extract_exists_pre; intros thread_func_.

  destruct split_Tsh as (sh_thr1 & sh_thr2 & Rsh_thr1 & Rsh_thr2 & Join_thr).
  rewrite <- (lock_inv_share_join _ _ _ _ _ Join_thr).
  
  (*pose (spawned_precondition := 
    fun (addof_ctr_lock: val) (addof_ctr: val)(v : val)( sh_ctr sh_thr : share)( arg_:val) =>
    `(lock_inv sh_ctr addof_ctr_lock (counter_invariant ctr_context_)) *
                   `(lock_inv sh_thr arg_ (thread_invariant ctr_context_ sh_ctr))). *)
  normalize.

  Definition SpwnPre context_ :=
  (EX sh_thr: share,
   EX sh_ctr: share,
      lock_inv sh_thr context_ (thread_invariant context_ sh_ctr) &&
      !!readable_share sh_thr *
      lock_inv sh_ctr (offset_val (Int.repr 32) context_) (counter_invariant context_) &&
      !!readable_share sh_ctr).

  Definition SpwnPost context_ :=
   (EX sh_thr: share,
    EX sh_ctr: share,
       lock_inv sh_thr context_ (thread_invariant context_ sh_ctr) &&
                !!readable_share sh_thr).
  
  Definition PrePost := fun y => (SpwnPre y, SpwnPost y).
(*eapply semax_seq'.

let Frame := fresh "Frame" in
evar (Frame: list (mpred)).



{ eapply (semax_call_id00_wow witness Frame).
  - reflexivity.
  - simpl. f_equal.
    (*unfold spawned_function_arg_type.  
    rewrite __AXIOM__.    
    unfold thread_func_spec; simpl.
     reflexivity.*)
  - reflexivity.
  - reflexivity.
  - prove_local2ptree.
  - repeat constructor.
  - entailer.
  - reflexivity.
  - prove_local2ptree.
  - Lemma exp_fun_comm A B P : (fun b : B => (EX a : A, (P a b))) = exp P.
    Proof.
      extensionality b.
      apply pred_ext; entailer.
      unfold exp; simpl.
      apply exp_right with a; auto.
    Qed.
    rewrite exp_fun_comm.
    Lemma exp_lift_comm A P : (EX x : A, `(P x)) = `(EX x : A, P x).
    Proof.
      apply pred_ext; entailer; eapply exp_right; eauto.
    Qed.
    rewrite exp_lift_comm.
    repeat constructor.
    
  - reflexivity.
  - reflexivity.
  - Forall_pTree_from_elements.
    generalize TC. destruct _id2; simpl; try solve[intro TC'; inversion TC'];
    (intros; rewrite true_eq; [eapply TT_right| reflexivity]).
  - Forall_pTree_from_elements.
  - unfold fold_right at 1 2; simpl; cancel .
    do 2 rewrite exp_sepcon1.
    rewrite __AXIOM1__, __AXIOM2__.
    apply @exp_right with _context.
    cancel.
    rewrite exp_sepcon1.
    apply @exp_right with sh1.
    rewrite (sepcon_comm (lock_inv sh1 ctr_context_ Rlock_placeholder && !!readable_share sh1)).
    rewrite (sepcon_assoc _ (lock_inv sh1 ctr_context_ Rlock_placeholder && !!readable_share sh1)).
    rewrite exp_sepcon1.
    apply @exp_right with sh1.
    entailer; cancel.
  - cbv beta iota; 
    repeat rewrite exp_uncurry;
    try rewrite no_post_exists0; 
    first [reflexivity | extensionality; simpl; reflexivity] .
  - intros; try match goal with  |- extract_trivial_liftx ?A _ =>
        (has_evar A; fail 1) || (repeat constructor)
     end. 
  - unify_postcondition_exps.
  - unfold fold_right_and; repeat rewrite and_True; auto.
} *)


  (*CALL: spwan*)

  forward_call_threadlib (thread_func_, ctr_context_) PrePost;
  unfold PrePost.
(*forward_call (thread_func_, ctr_context_).*)
{
    - Lemma exp_fun_comm A B P : (fun b : B => (EX a : A, (P a b))) = exp P.
    Proof.
      extensionality b.
      apply pred_ext; entailer.
      unfold exp; simpl.
      apply exp_right with a; auto.
    Qed.
    simpl.
    rewrite exp_fun_comm.
    Lemma exp_lift_comm A P : (EX x : A, `(P x)) = `(EX x : A, P x).
    Proof.
      apply pred_ext; entailer; eapply exp_right; eauto.
    Qed.
    rewrite exp_lift_comm.
    repeat constructor.
}
{
    generalize TC. destruct _id2; simpl; try solve[intro TC'; inversion TC'];
                   (intros; rewrite true_eq; [eapply TT_right| reflexivity]).
}
{ unfold SpwnPre, SpwnPost; simpl.
  do 2 rewrite exp_sepcon1.
  apply @exp_right with _context.
  cancel.
  normalize.
  apply @exp_right with sh_thr1.
  normalize.
  apply @exp_right with sh_ctr1.
  entailer; cancel.
}

(*
(*CALL: concurrent_incr*)

simpl.
forward_call  ( ctr_, (offset_val (Int.repr 32) ctr_context_), sh2).
 *)

(*CALL: acquire *)
forward_call_threadlib ((offset_val (Int.repr 32) ctr_context_), sh_ctr2) (counter_invariant ctr_context_).
(*forward_call  ( (offset_val (Int.repr 32) ctr_context_), sh1).*)
unfold counter_invariant.
normalize. intros z.
normalize. intros ctr.
normalize. 

(*COMMAND: ctr = ctr_context->ctr;*)
forward.

(*CALL: incr*)
forward_call (z, ctr, Tsh).

(*CALL: incr*)
rewrite (field_at_data_at _ _ [StructField _ctr]).

(*CALL: release*)
  
(*rewrtie 
forward_call ().*)
forward_call_threadlib ((offset_val (Int.repr 32) ctr_context_), sh_ctr2) (counter_invariant ctr_context_).
(*forward_call  ( (offset_val (Int.repr 32) ctr_context_), sh1). *)
unfold counter_invariant.
normalize.
eapply (exp_right (Int.add z Int.one)).
normalize.
eapply (exp_right ctr).
  rewrite (field_at_data_at _ _ [StructField _ctr]).
entailer; cancel.


(*CALL: acquire *)
forward_call_threadlib (ctr_context_ , sh_thr2)
                       (thread_invariant ctr_context_ sh_ctr1).
(*forward_call  ( ctr_context_ , sh2).*)


(*CALL: acquire *)
forward_call_threadlib ((offset_val (Int.repr 32) ctr_context_), sh_ctr2) (counter_invariant ctr_context_).
(*forward_call  (  (offset_val (Int.repr 32) ctr_context_) , sh1).*)
unfold counter_invariant.
normalize. intros z1.
normalize. intros ctr1.
normalize.

(* COMMAND: ctr = ctr_context->ctr; *)
forward.

(*CALL: read*)
forward_call (z1, ctr1, Tsh) t.
try rewrite H4 in *; clear H4 t.

 (*RETURN*)
forward.
eapply (exp_right _id). normalize.
eapply (exp_right _id0). normalize. entailer.
admit.
Qed.
