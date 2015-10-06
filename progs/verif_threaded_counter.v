Require Import floyd.proofauto.
Load threaded_counter.

Local Open Scope logic.


Instance CompSpecs : compspecs.
Proof. make_compspecs prog. Defined.  

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
   PRE [ _ctr_lock OF tptr tlock ]
     PROP (readable_share sh)
     LOCAL (temp _ctr_lock v)
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

Definition spawn_thread_spec := (* universe inconsistency if "WITH P" *)
  DECLARE _spawn_thread
   WITH f : val, b : val
   PRE [_thread_func OF tptr voidstar_funtype, _thread_mutex OF tptr tvoid]
     PROP ()
     LOCAL (temp _thread_mutex b)
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
   WITH  addof_ctr_lock: val, addof_ctr: val,v : val, sh : share
   PRE [ ]
     PROP (readable_share sh) (*Holds partial ownerchip of ctr lock*)
     LOCAL (gvar _ctr addof_ctr; gvar _ctr_lock addof_ctr_lock; gvar _ctr_lock v)
     SEP (`(lock_inv sh v Rlock_placeholder))
   POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP ().

Definition thread_func_spec :=
  DECLARE _thread_func
   WITH z: int
   PRE [ ]
     PROP () (*Holds partial ownerchip of two locks*)
     LOCAL ()
     SEP ()
   POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP ().

Definition main_spec :=
 DECLARE _main
  WITH  z0 : int, z1 : int, addof_ctr: val, ctr: val
  PRE  [] 
        PROP ()
        LOCAL(gvar _ctr addof_ctr)
        SEP(`(data_at Ews tint (repinj tint z0) ctr);`(data_at Ews (tptr tint) ctr addof_ctr))
  POST [tint]
        PROP()
        LOCAL( temp ret_temp (Vint (Int.repr 2)))
        SEP(`(data_at Ews tint (repinj tint z1) ctr);`(data_at Ews (tptr tint) ctr addof_ctr)).

Definition Vprog : varspecs := (_ctr_lock, tlock)::(_ctr, tptr tint)::(_zero,tint)::nil.

Definition Gprog : funspecs :=
  counter_funspecs ++ threads_funspecs ++ concurrent_incr_spec:: thread_func_spec::main_spec::nil.


(*Lets do this first:*)
Lemma body_concurrent_incr:  semax_body Vprog Gprog f_concurrent_incr concurrent_incr_spec.
  start_function.
  forward _ctr_lock_ptr.
  forward_call' (v, sh) r.
  forward_call' (_ctr_lock_ptr).
 
 forward thread_mutex_ptr_.
 forward.

Proof.

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