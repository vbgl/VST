Require Import floyd.proofauto.
Load threaded_counter2.

Local Open Scope logic.


Instance CompSpecs : compspecs.
Proof. make_compspecs prog. Defined.  

Definition t_struct_mutex1 := Tstruct _ctr_lock noattr.

(* Sequential stuff *)

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


(* Threads specifications*)

Definition tlock := Tstruct _lock_t noattr.
Axiom lock_inv : share -> val -> mpred -> mpred.

Axiom lock_inv_share_join : forall sh1 sh2 sh v R, sepalg.join sh1 sh2 sh ->
  lock_inv sh1 v R * lock_inv sh2 v R = lock_inv sh v R.

Parameter Rlock_placeholder : mpred.
Parameter spawned_precondition_placeholder : val -> mpred.
Parameter spawned_postcondition_placeholder : val -> mpred.
Definition voidstar_funtype :=
  Tfunction
    (Tcons (tptr tvoid) Tnil)
    (tptr tvoid)
    cc_default.

Definition makelock_spec :=
  DECLARE _makelock
   WITH v : val, sh : share
   PRE [ _ctr_lock OF tptr tlock ]
     PROP (writable_share sh)
     LOCAL (temp _ctr_lock v)
     (* SEP (`(mapsto_ Tsh tlock v)) *)  (* ask andrew: that, or mapsto ... (default_val tlock) ? *)
     SEP (`(data_at_ Tsh tlock v))
   POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (`(lock_inv Tsh v Rlock_placeholder)).

Definition acquire_spec :=
  DECLARE _acquire
   WITH v : val, sh : share
   PRE [ _ctr_lock_ptr OF tptr tlock ]
     PROP (readable_share sh)
     LOCAL (temp _ctr_lock_ptr v)
     SEP (`(lock_inv sh v Rlock_placeholder))
   POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (`(lock_inv sh v Rlock_placeholder) ; `Rlock_placeholder).

Definition release_spec :=
  DECLARE _release
   WITH v : val, sh : share
   PRE [ _ctr_lock OF tptr tlock ]
     PROP (readable_share sh)
     LOCAL (temp _ctr_lock v)
     SEP (`(lock_inv sh v Rlock_placeholder) ; `Rlock_placeholder)
   POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (`(lock_inv sh v Rlock_placeholder)).

Parameter spawn_gvars : list (environ -> Prop).

Definition spawn_thread_spec  := (* universe inconsistency if "WITH P" *)
  DECLARE _spawn_thread
   WITH f : val, b : val
   PRE [_thread_func OF tptr voidstar_funtype, _ctr_context OF tptr tvoid]
     PROP ()
     (LOCAL (temp _ctr_context b)
     SEP ((EX _y : ident,
     `(func_ptr'
       (WITH y : val
        PRE [ _y OF tptr tvoid ]
          PROP  ()
          (LOCAL (temp _y y)
          SEP   (`(spawned_precondition_placeholder y)))
        POST [tvoid]
          PROP  ()
          LOCAL ()
          SEP   (`(spawned_postcondition_placeholder y))
       )
       f)) ; `(spawned_precondition_placeholder b)))
   POST [ tvoid ]
     PROP  ()
     LOCAL ()
     SEP   (emp).

Definition funspec_type f_spec :=
  match f_spec with mk_funspec _ A P Q => A end.

Definition funspec_pre f_spec: funspec_type f_spec -> environ -> mpred :=
  match f_spec with mk_funspec _ A P Q => P end.

Definition funspec_post f_spec: funspec_type f_spec -> environ -> mpred:=
  match f_spec with mk_funspec _ A P Q => Q end.


Parameter spawned_function_funspec : funspec.
Definition spawned_function_arg_type: Type := funspec_type spawned_function_funspec.

Definition spawn_thread_spec' := (* universe inconsistency if "WITH P" *)
  DECLARE _spawn_thread
   WITH f : val, args_ : spawned_function_arg_type
   PRE [_thread_func OF tptr voidstar_funtype, _ctr_context OF tptr tvoid]
     PROP ()
     LOCAL ()
     SEP (`(func_ptr' spawned_function_funspec f) ; (funspec_pre spawned_function_funspec args_))
   POST [ tvoid ]
     PROP  ()
     LOCAL ()
     SEP   (emp).

Definition threads_funspecs : funspecs :=
  makelock_spec ::
(*  freelock_spec :: *)
  acquire_spec ::
  release_spec ::
  spawn_thread_spec ::
  (*  exit_thread_spec ::*)
  nil.

(* Threaded part*)
(*Definition concurrent_incr_spec :=
  DECLARE _concurrent_incr
   WITH   addof_ctr: val, addof_ctr_lock: val, sh : share
   PRE [ _ctr OF tptr tint, _ctr_lock_ptr OF tptr tlock ]
     PROP (readable_share sh) (*Holds partial ownerchip of ctr lock*)
     LOCAL (temp _ctr addof_ctr; temp _ctr_lock_ptr addof_ctr_lock)
     SEP (`(lock_inv sh addof_ctr_lock Rlock_placeholder))
   POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (`(lock_inv sh addof_ctr_lock Rlock_placeholder)).*)


Definition thread_invariant v:=
  EX sh:share,
  (lock_inv sh v Rlock_placeholder).

Definition thread_func_spec :=
  DECLARE _thread_func
  WITH  context_:val
   PRE [_context OF tptr tvoid]
     PROP () (*Holds partial ownerchip of two locks*)
     LOCAL (temp _context context_)
     SEP ( `(EX sh_thr: share,
                        lock_inv sh_thr context_ Rlock_placeholder &&
                                 !!readable_share sh_thr *
           EX sh_ctr: share,
                        lock_inv sh_ctr (offset_val (Int.repr 32) context_) Rlock_placeholder &&
                                 !!readable_share sh_ctr))
   POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (`(EX sh_thr: share,
                        lock_inv sh_thr context_ Rlock_placeholder &&
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
        LOCAL( temp ret_temp (Vint (Int.repr 2)))
        SEP(  `(data_at Ews tint (repinj tint z) ctr)).

Definition main_spec' :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog u
  POST [ tint ] main_post prog u.

(* Malloc *)

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
  counter_funspecs ++ threads_funspecs ++ (*concurrent_incr_spec::*)
                   malloc_spec :: thread_func_spec::main_spec::nil.


(*Lets do this first:*)

Definition counter_invariant addof_ctr:=
  EX z : int, EX ctr : val, 
   (data_at Ews tint (repinj tint z) ctr)*(data_at Ews (tptr tint) ctr addof_ctr).



(*
Lemma body_concurrent_incr:  semax_body Vprog Gprog f_concurrent_incr concurrent_incr_spec.
  start_function.

  
  forward _ctr_lock_ptr.
  
  (*call Acquire *)
  (*drop_LOCAL 2%nat. I don't understand why this condition breaks the fwd call*)
  forward_call (addof_ctr_lock, sh).

  
  (*call incr*)

  (* The invariant can't be set up 'legaly' because of universe inconsistency *)
  assert (__AXIOM0__: Rlock_placeholder = (counter_invariant addof_ctr)) by admit.
  rewrite __AXIOM0__.
  unfold counter_invariant at 2.

  
  normalize; intros z.
  normalize; intros ctr.
  normalize.
  
  forward_call ((Int.repr z), addof_ctr, ctr).

  (*call Release *)
  forward_call (addof_ctr_lock, sh).
  rewrite HH.
  cancel.
  unfold counter_invariant.
  normalize.
  entailer.
  apply exp_right with (z+1).
  normalize.
  rewrite <- add_repr; simpl.
  fold Int.one.
  apply exp_right with ctr.
  cancel.

  forward.
Qed.*)

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
  forward_call  ( (offset_val (Int.repr 32) context_), sh_ctr).
  
  (*COMMAN: int *ctr = ctr_context->ctr; *)
  Definition counter_invariant' field_ctr:=
  EX z : int, EX ctr : val,
                       (data_at Tsh tint (repinj tint z) ctr)*
                       (field_at Tsh (Tstruct _ctr_context noattr) [StructField _ctr] ctr field_ctr).
  assert (__AXIOM0__: Rlock_placeholder = (counter_invariant' context_)) by admit.
  rewrite __AXIOM0__ at 2. unfold counter_invariant'.
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
           Rlock_placeholder); `(counter_invariant' context_);
                     `(lock_inv sh_thr context_ Rlock_placeholder))))).
  entailer. cancel.
  unfold counter_invariant'; normalize.
  eapply (exp_right (Int.add z Int.one)). normalize.
  eapply (exp_right (eval_id _ctr rho)). normalize.
  
  (*CALL: release ctr*)
  rewrite <- __AXIOM0__.
  forward_call ((offset_val (Int.repr 32) context_), sh_ctr).
  
  (*call release*)
  assert (__AXIOM1__: Rlock_placeholder =  lock_inv sh_ctr (offset_val (Int.repr 32) context_) Rlock_placeholder) by admit.
  forward_call (context_, sh_thr).
  rewrite __AXIOM1__ at 2; cancel.
  
  forward.
  eapply (exp_right sh_thr).
  entailer.
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
  forward_call ((offset_val (Int.repr 32) ctr_context_) , Tsh). 

  (*call release(&ctr_lock)*)
  assert (__AXIOM0__: Rlock_placeholder = (counter_invariant' ctr_context_)) by admit.
  forward_call ((offset_val (Int.repr 32) ctr_context_) , Tsh).

  rewrite __AXIOM0__.
  unfold counter_invariant'.
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
  
  normalize.
  forward_call (ctr_context_ , Tsh).
  
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


Ltac get_global_function'' _f :=
  eapply (semax_fun_id'' _f); try reflexivity.
  
  get_global_function'' _thread_func.
  normalize.
  apply extract_exists_pre; intros thread_func_.








(*
  
  (*SEMAX RULE for spawn*)
  Definition spawn_expr name:=
    (Evar name  (* Name is an identifier, that in the future will be fixed. *)
          (Tfunction (* It's a function, under the hood *)
             (Tcons (tptr (Tfunction (Tcons (tptr tvoid) Tnil)  (tptr tvoid) cc_default)) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)).
  
  Definition Sspawn' name f arg:=
    Scall                      (* Clighen comiles spawn as a function. *)
      None                     (* Spawning doesn't return anything. *)
      (spawn_expr name)        (* The typed expression of spawn as a function*)
      [f; arg]  (* One single argument of type (void * ) *)
  .







  
  (*Have to do this in every file using the rule, until the function gets a fixed name. *)
  Definition Sspawn:= Sspawn' _spawn_thread.
  
Axiom semax_spawn : 
  forall {Espec: OracleKind}{CS: compspecs},
  forall Delta A (P Q: A -> environ -> mpred) (x: A) (F: environ -> mpred)
          arg_name a b,
           Cop.classify_fun (typeof a) =
           Cop.fun_case_f (type_of_params [(arg_name , tptr tvoid)]) tvoid cc_default ->
          tc_fn_return Delta None tvoid ->
  @semax CS Espec Delta
          ((tc_expr Delta a) && (tc_expr Delta b)  && 
         (`(func_ptr (mk_funspec  ([(arg_name , tptr tvoid)],tvoid) A P Q)) (eval_expr a) &&   
          (F * `(P x) (make_args' ([(arg_name , tptr tvoid)],tvoid) (fun env=> [eval_expr b env])))))
         (Sspawn a b)
         (normal_ret_assert  
            ( F )).


eapply semax_seq'.
unfold PROPx, LOCALx, SEPx; simpl.
normalize.
rewrite local_lift2_and.
assert ().
rewrite andp_unfold.
repeat rewrite <- andp_assoc.
unfold fold_right.
repeat rewrite local_lift2_and.
unfold func_ptr'.
rewrite local_unfold.
repeat rewrite local_unfold.
lift1.
eapply semax_spawn.


  
  (* build the spawned frame *)
  
Axiom semax_spawn : 
  forall {Espec: OracleKind}{CS: compspecs},
    forall Delta A (P Q: A -> environ -> mpred) (x: A) (F: environ -> mpred) ret argsig retsig a bl,
           Cop.classify_fun (typeof a) =
           Cop.fun_case_f (type_of_params argsig) retsig cc_default ->
           (retsig = Tvoid -> ret = None) ->
          tc_fn_return Delta ret retsig ->
  @semax CS Espec Delta
          ((tc_expr Delta a) && (tc_exprlist Delta (snd (split argsig)) bl)  && 
         (`(func_ptr (mk_funspec  (argsig,retsig) A P Q)) (eval_expr a) &&   
          (F * `(P x) (make_args' (argsig,retsig) (eval_exprlist (snd (split argsig)) bl)))))
         (Scall ret a bl)
         (normal_ret_assert  
          (EX old:val, substopt ret (`old) F * maybe_retval (Q x) retsig ret)).
*)


  
  destruct split_Tsh as (sh1 & sh2 & Rsh1 & Rsh2 & Join).
  rewrite <- (lock_inv_share_join _ _ _ _ _ Join).
  rewrite <- (lock_inv_share_join _ _ _ _ _ Join).
  
  pose (spawned_precondition := 
    fun (addof_ctr_lock: val) (addof_ctr: val)(v : val)( sh : share)( arg_:val) =>
    `(lock_inv sh addof_ctr_lock Rlock_placeholder) *
                   `(lock_inv sh arg_ Rlock_placeholder)).
  normalize.

assert (__AXIOM__: spawned_function_funspec =  snd thread_func_spec) by admit.
    assert (__AXIOM1__:
              spawned_precondition_placeholder =
              fun context_ =>
                (EX sh_thr: share,
                        lock_inv sh_thr context_ Rlock_placeholder &&
                                 !!readable_share sh_thr *
           EX sh_ctr: share,
                        lock_inv sh_ctr (offset_val (Int.repr 32) context_) Rlock_placeholder &&
                                 !!readable_share sh_ctr) ) by admit.
    
    assert (__AXIOM2__:
              spawned_postcondition_placeholder =
              fun context_ =>
                (EX sh_thr: share,
                        lock_inv sh_thr context_ Rlock_placeholder &&
                                 !!readable_share sh_thr)) by admit.  

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
forward_call (thread_func_, ctr_context_).
{
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
}
{
    generalize TC. destruct _id2; simpl; try solve[intro TC'; inversion TC'];
                   (intros; rewrite true_eq; [eapply TT_right| reflexivity]).
}
{ rewrite __AXIOM1__, __AXIOM2__.
  do 2 rewrite exp_sepcon1.
  apply @exp_right with _context.
  cancel.
  normalize.
  apply @exp_right with sh1.
  normalize.
  apply @exp_right with sh2.
  entailer; cancel.
}

(*
(*CALL: concurrent_incr*)

simpl.
forward_call  ( ctr_, (offset_val (Int.repr 32) ctr_context_), sh2).
 *)

(*CALL: acquire *)
forward_call  ( (offset_val (Int.repr 32) ctr_context_), sh1).
rewrite __AXIOM0__ at 2. unfold counter_invariant'.
normalize. intros z.
normalize. intros ctr.
normalize. 

(*COMMAND: ctr = ctr_context->ctr;*)
forward blah. rewrite H4 in *; clear H4.

(*CALL: incr*)
forward_call (z, ctr, Tsh).

  (*CALL: incr*)
  rewrite (field_at_data_at _ _ [StructField _ctr]).

  (*CALL: release*)
  
(*rewrtie 
forward_call ().*)

forward_call  ( (offset_val (Int.repr 32) ctr_context_), sh1).
rewrite __AXIOM0__ at 2. unfold counter_invariant'.
normalize.
eapply (exp_right (Int.add z Int.one)).
normalize.
eapply (exp_right ctr).
  rewrite (field_at_data_at _ _ [StructField _ctr]).
entailer; cancel.


(*CALL: acquire *)
forward_call  ( ctr_context_ , sh2).


(*CALL: acquire *)
forward_call  (  (offset_val (Int.repr 32) ctr_context_) , sh1).
rewrite __AXIOM0__ at 2. unfold counter_invariant'.
normalize. intros z1.
normalize. intros ctr1.
normalize.


(* COMMAND: ctr = ctr_context->ctr; *)
forward blah1.
try rewrite H4 in *; clear H4 blah1.

(*CALL: read*)
forward_call (z1, ctr1, Tsh) t.
try rewrite H4 in *; clear H4 t.

 (*RETURN*)
forward.
admit.
Qed.
