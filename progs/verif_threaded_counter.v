Require Import floyd.proofauto.
Load threaded_counter.

Local Open Scope logic.


Instance CompSpecs : compspecs.
Proof. make_compspecs prog. Defined.  

Definition t_struct_mutex1 := Tstruct _ctr_mutex noattr.

Definition t_struct_zero := Tstruct _zero noattr.
Definition t_struct_ctr := Tstruct _ctr noattr.

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
        LOCAL()
        SEP()
  POST [tvoid]
        PROP()
        LOCAL()
        SEP().

Definition main_spec :=
 DECLARE _main
  WITH z0 : int, z1 : int, addof_ctr: val, ctr: val
  PRE  [] 
        PROP ()
        LOCAL(gvar _ctr addof_ctr)
        SEP(`(data_at Ews tint (repinj tint z0) ctr);`(data_at Ews (tptr tint) ctr addof_ctr))
  POST [tint]
        PROP()
        LOCAL( temp ret_temp (Vint (Int.repr 2)))
        SEP(`(data_at Ews tint (repinj tint z1) ctr);`(data_at Ews (tptr tint) ctr addof_ctr)).

Definition Vprog : varspecs := (_ctr_mutex, )::(_ctr, tptr tint)::(_zero,tint)::nil.

Definition Gprog : funspecs := 
  reset_spec::incr_spec::read_spec::main_spec::nil.

Definition main_spec :=
 DECLARE _main
  WITH z : int, addof_ctr: val, ctr: val
  PRE  [] 
        PROP ()
        LOCAL(gvar _counter addof_ctr)
        SEP(`(data_at Ews tint (repinj tint z) ctr);`(data_at Ews (tptr tint) ctr addof_ctr))
  POST [tint]
        PROP()
        LOCAL( temp ret_temp (Vint (Int.one)))
        SEP(`(data_at Ews tint (repinj tint z) ctr);`(data_at Ews (tptr tint) ctr addof_ctr)).

Definition Vprog : varspecs := (_counter, tptr tint)::nil.

Definition Gprog : funspecs := 
  main_spec::nil.

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