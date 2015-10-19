Require Import floyd.proofauto.
Require Import progs.threadlib.
Load threaded_counter.

Local Open Scope logic.

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




Definition t_struct_mutex1 := Tstruct _ctr_lock noattr.

Definition t_struct_zero := Tstruct _zero noattr.
Definition t_struct_ctr := Tstruct _ctr noattr.

(* Sequential stuff *)

Definition reset_spec :=
 DECLARE _reset
  WITH z : int, addof_ctr: val, ctr: val
  PRE  [] 
        PROP ()
        LOCAL(gvar _ctr addof_ctr)
        SEP(`(data_at Ews tint (repinj tint z) ctr);`(data_at Ews (tptr tint) ctr addof_ctr))
  POST [tvoid]
        PROP()
        LOCAL()
        SEP(`(data_at Ews tint (repinj tint Int.zero) ctr);`(data_at Ews (tptr tint) ctr addof_ctr)).

Definition read_spec :=
 DECLARE _read
  WITH z : int, addof_ctr: val, ctr: val
  PRE  [] 
        PROP ()
        LOCAL(gvar _ctr addof_ctr)
        SEP(`(data_at Ews tint (repinj tint z) ctr);`(data_at Ews (tptr tint) ctr addof_ctr))
  POST [tint]
        PROP()
        LOCAL( temp ret_temp (Vint z))
        SEP(`(data_at Ews tint (repinj tint z) ctr);`(data_at Ews (tptr tint) ctr addof_ctr)).

Definition incr_spec :=
 DECLARE _incr
  WITH z : int, addof_ctr: val, ctr: val
  PRE  [] 
        PROP ()
        LOCAL(gvar _ctr addof_ctr)
        SEP(`(data_at Ews tint (repinj tint z) ctr);`(data_at Ews (tptr tint) ctr addof_ctr))
  POST [tvoid]
        PROP()
        LOCAL()
        SEP(`(data_at Ews tint (repinj tint (Int.add z Int.one)) ctr);`(data_at Ews (tptr tint) ctr addof_ctr)).

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
   PRE [_thread_func OF tptr voidstar_funtype, _thread_mutex_ptr OF tptr tvoid]
     PROP ()
     (LOCALx (temp _thread_mutex_ptr b::spawn_gvars)
     SEP ((EX _y : ident,
     `(func_ptr'
       (WITH y : val
        PRE [ _y OF tptr tvoid ]
          PROP  ()
          (LOCALx (temp _y y::spawn_gvars)
          SEP   (`(spawned_precondition_placeholder y)))
        POST [tvoid]
          PROP  ()
          LOCAL ()
          SEP   (emp)
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
   PRE [_thread_func OF tptr voidstar_funtype, _thread_mutex_ptr OF tptr tvoid]
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
Definition concurrent_incr_spec :=
  DECLARE _concurrent_incr
   WITH  addof_ctr_lock: val, addof_ctr: val, sh : share
   PRE [ ]
     PROP (readable_share sh) (*Holds partial ownerchip of ctr lock*)
     LOCAL (gvar _ctr addof_ctr; gvar _ctr_lock addof_ctr_lock)
     SEP (`(lock_inv sh addof_ctr_lock Rlock_placeholder))
   POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (`(lock_inv sh addof_ctr_lock Rlock_placeholder)).

Definition thread_invariant v:=
  EX sh:share,
  (lock_inv sh v Rlock_placeholder).

Definition thread_func_spec :=
  DECLARE _thread_func
  WITH  addof_ctr_lock: val, addof_ctr: val, arg_:val, sh : share
   PRE [_arg OF tptr tvoid]
     PROP () (*Holds partial ownerchip of two locks*)
     LOCAL (temp _arg arg_; gvar _ctr addof_ctr; gvar _ctr_lock addof_ctr_lock)
     SEP (`(lock_inv sh addof_ctr_lock Rlock_placeholder); `(lock_inv sh arg_ Rlock_placeholder);
         `(!!readable_share sh))
   POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (`(lock_inv sh arg_ Rlock_placeholder)).

Definition main_spec :=
 DECLARE _main
  WITH z0: int, addof_ctr: val, addof_ctr_lock: val, ctr: val
  PRE  [] 
        PROP ()
        LOCAL(gvar _ctr addof_ctr; gvar _ctr_lock addof_ctr_lock)
        SEP( `(data_at Ews tint (repinj tint z0) ctr);`(data_at Ews (tptr tint) ctr addof_ctr);
           `(data_at_ Tsh tlock addof_ctr_lock))
  POST [tint]
  EX z1:int,
        PROP()
        LOCAL( temp ret_temp (Vint (Int.repr 2)))
        SEP( `(data_at Ews tint (repinj tint z1) ctr);`(data_at Ews (tptr tint) ctr addof_ctr)).

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

Definition Vprog : varspecs := (_ctr_lock, tlock)::(_ctr, tptr tint)::(_zero,tint)::nil.

Definition Gprog : funspecs :=
  counter_funspecs ++ threads_funspecs ++ concurrent_incr_spec::
                   malloc_spec :: thread_func_spec::main_spec::nil.


(*Lets do this first:*)

Definition counter_invariant addof_ctr:=
  EX z : Z, EX ctr : val, 
   (data_at Ews tint (repinj tint (Int.repr z)) ctr)*(data_at Ews (tptr tint) ctr addof_ctr).

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  
  (*call reset*)
  forward_call  (z0 , addof_ctr, ctr).

  (*call makelock(&ctr_lock)*)
  pose (sh := Share.top).
  assert (Wsh: writable_share sh) by apply semax_call.writable_share_top.
  normalize.
  forward_call (addof_ctr_lock , sh).

  (*call release(&ctr_lock)*)
  assert (RLock_ctr: Rlock_placeholder = (counter_invariant addof_ctr)) by admit.
  forward_call (addof_ctr_lock , sh).
  rewrite RLock_ctr.
  unfold counter_invariant.
  normalize. apply exp_right with (0).
  normalize. apply exp_right with ctr.
  fold Int.zero. cancel.

  (*call malloc(thread_mutex_ptr)*)
  (* rewrite <- seq_assoc. *)
  normalize.
  forward_call 24%Z _thread_mutex_ptr.
  solve [compute; intuition; congruence].
  
  (*call makelock(&thread_mutex)*)
  normalize.
  forward_call (_thread_mutex_ptr , sh).
  rewrite <- memory_block_data_at_; simpl.
  cancel.
   (* Proof field_compatible tlock [] _thread_mutex_ptr*) 
  {
  unfold malloc_compatible in H; destruct _thread_mutex_ptr; try solve[inversion H].
  unfold field_compatible; intuition.
  - unfold isptr; auto.
  - compute; reflexivity.
  - simpl. omega.
  - simpl. unfold align_attr, attr_alignas, noattr.
    eapply (Zdivides_trans _ 8 _). exists 2; omega. exact H0.
  - simpl; trivial.
  }

  (*call spawn*)

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
  
  pose (spawned_precondition := 
    fun (addof_ctr_lock: val) (addof_ctr: val)(v : val)( sh : share)( arg_:val) =>
    `(lock_inv sh addof_ctr_lock Rlock_placeholder) *
                   `(lock_inv sh arg_ Rlock_placeholder)).
  normalize.

assert (__AXIOM1__: spawned_function_funspec =  snd thread_func_spec) by admit.
assert (__AXIOM2__: spawn_gvars =  [gvar _ctr addof_ctr; gvar _ctr_lock addof_ctr_lock]) by admit.

  pose (witness:= (thread_func_, (addof_ctr_lock,  addof_ctr, _thread_mutex_ptr,sh ))).
  eapply semax_seq'.

let Frame := fresh "Frame" in
evar (Frame: list (mpred)).



{ eapply (semax_call_id00_wow witness Frame).
  - reflexivity.
  - simpl. f_equal.
    unfold spawned_function_arg_type. rewrite __AXIOM__.
    unfold thread_func_spec; simpl.
    f_equal; reflexivity.
  - reflexivity.
  - reflexivity.
  - prove_local2ptree.
  - repeat constructor.
  - entailer.
  - reflexivity.
  - prove_local2ptree.
  - repeat constructor.
    unfold PROPx, LOCALx, SEPx; simpl.
    unfold local, lift1.
    econstructor.
    simpl.
    
    entailer.
  - reflexivity.

    
try reflexivity.
reflexivity.

 [ reflexivity | reflexivity | reflexivity | reflexivity
 | prove_local2ptree | repeat constructor 
 | try apply local_True_right; entailer!
 | reflexivity
 | prove_local2ptree | repeat constructor 
 | reflexivity | reflexivity
 | Forall_pTree_from_elements
 | Forall_pTree_from_elements
 | unfold fold_right at 1 2; cancel
 | cbv beta iota; 
    repeat rewrite exp_uncurry;
    try rewrite no_post_exists0; 
    first [reflexivity | extensionality; simpl; reflexivity]
 | intros; try match goal with  |- extract_trivial_liftx ?A _ =>
        (has_evar A; fail 1) || (repeat constructor)
     end
 | unify_postcondition_exps
 | unfold fold_right_and; repeat rewrite and_True; auto
 ].

Ltac simpl_strong_cast :=
try match goal with |- context [strong_cast ?t1 ?t2 ?v] =>
  first [change (strong_cast t1 t2 v) with v
         | change (strong_cast t1 t2 v) with
                (force_val (sem_cast t1 t2 v))
          ]
end.

  
  forward_call_id00_wow (thread_func_, _thread_mutex_ptr).
          | after_forward_call ]
  
  eapply semax_seq'.
             forward_call_id1_wow witness.
           | forward_call_id1_x_wow witness
           | forward_call_id1_y_wow witness
           | forward_call_id01_wow witness ]
     | after_forward_call
     ]
  |  eapply semax_seq'; [forward_call_id00_wow witness 
          | after_forward_call ]
  | rewrite <- seq_assoc; fwd_call' witness
  ].


  
  
  fwd_call' (thread_func_, _thread_mutex_ptr).
  forward_call (thread_func_, _thread_mutex_ptr).


Definition spawn_thread_spec := (* universe inconsistency if "WITH P" *)
  DECLARE _spawn_thread
   WITH f : val, _thread_mutex_ptr : val
   PRE [_thread_func OF tptr voidstar_funtype, Top._thread_mutex_ptr OF tptr tvoid]
     PROP ()
     LOCAL (temp Top._thread_mutex_ptr _thread_mutex_ptr)
     SEP ((EX _y : ident,
     `(func_ptr'
       (WITH y : val * val * share * val
        PRE [ _y OF tptr tvoid ]
          (let (p, arg_) := x in
            let (p0, sh0) := p in
            let (addof_ctr_lock0, addof_ctr0) := p0 in
          PROP  ()
          LOCAL (temp _arg y)
          SEP   (`(spawned_precondition_placeholder y)))
        POST [tvoid]
          PROP  ()
          LOCAL ()
          SEP   (emp)
       )
       f)) ; `(spawned_precondition_placeholder _thread_mutex_ptr))
   POST [ tvoid ]
     PROP  ()
     LOCAL ()
     SEP   (emp).



  
  
Lemma body_thread_func_spec:semax_body Vprog Gprog f_thread_func thread_func_spec.
Proof.
  start_function.
  normalize.

  forward. 

  (*call concurrent_incr*)
  forward_call (addof_ctr_lock, addof_ctr, sh).

  (* The invariant can't be set up 'legaly' because of universe inconsistency *)
  assert (RLock_thr: Rlock_placeholder = thread_invariant addof_ctr_lock) by admit.

  (*call release*)
  forward_call (arg_, sh).
  rewrite RLock_thr at 2. unfold thread_invariant.
  normalize. 
  apply exp_right with (sh). cancel.

  forward.
Qed.

Lemma body_concurrent_incr:  semax_body Vprog Gprog f_concurrent_incr concurrent_incr_spec.
  start_function.
  forward _ctr_lock_ptr.
  
  (*call Acquire *)
  (*drop_LOCAL 2%nat. I don't understand why this condition breaks the fwd call*)
  forward_call (addof_ctr_lock, sh).

  
  (*call incr*)

  (* The invariant can't be set up 'legaly' because of universe inconsistency *)
  assert (RLock_ctr: Rlock_placeholder = (counter_invariant addof_ctr)) by admit.
  rewrite RLock_ctr.
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
Qed.

  


Lemma body_incr:  semax_body Vprog Gprog f_incr incr_spec.
Proof.
 start_function.
 name ctr_ _ctr.
 name ctr0_ _ctr0.
 name t_ _t.
 forward.
 forward.
 forward.
 forward.
unfold_repinj.
cancel.
apply derives_refl'. unfold data_at. f_equal. f_equal. f_equal.
unfold unfold_reptype'. simpl.
rewrite <- eq_rect_eq.
auto.
Qed.

Lemma body_reset:  semax_body Vprog Gprog f_reset reset_spec.
Proof.
 start_function.
 name ctr_ _ctr.
 name ctr0_ _ctr0.
 name t_ _t.
 forward.
 forward.
 forward.
unfold_repinj.
cancel.
Qed.


Lemma body_read:  semax_body Vprog Gprog f_read read_spec.
Proof.
 start_function.
 name ctr_ _ctr.
 name ctr0_ _ctr0.
 name t_ _t.
 forward.
 forward.
 forward. 
 unfold_repinj.
 apply andp_right; cancel.
 apply prop_right.
 revert H0; unfold_repinj. congruence.
Qed.


(*Threaded part*)
Lemma body_concurrent_incr:  semax_body Vprog Gprog f_concurrent_incr concurrent_incr_spec.
  start_function.
  forward_call' (_ctr_lock).
 
 forward thread_mutex_ptr_.
 forward.

Proof.

Lemma body_thread_incr:  semax_body Vprog Gprog f_thread_func thread_func_spec.
 start_function.
 forward thread_mutex_ptr_.
 forward.

Proof.


Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
 start_function.
 name ctr_ _counter.
 forward.
 eapply semax_seq.
 eapply semax_post.
 
 forward.
 
 forward_call' (z, addof_ctr, ctr).
 forward_call' (Int.zero, addof_ctr, ctr).
 forward_call' ((Int.add Int.zero Int.one), addof_ctr, ctr).
 forward_call' ((Int.add (Int.add Int.zero Int.one) Int.one), addof_ctr, ctr) r0.
 forward.
Qed.