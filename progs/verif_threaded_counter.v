Require Import floyd.proofauto.
Load threaded_counter.

Local Open Scope logic.

Definition t_struct_mutex1 := Tstruct _mutex1 noattr.
Definition t_struct_counter := Tstruct _counter noattr.

Definition incr_spec :=
 DECLARE _main
  WITH z : int, addof_ctr: val, ctr: val
  PRE  [] 
        PROP ()
        LOCAL(gvar _ctr addof_ctr)
        SEP(`(data_at Ews tint (repinj tint z) ctr);`(data_at Ews (tptr tint) ctr addof_ctr))
  POST [tint]
        PROP()
        LOCAL( temp ret_temp (Vint (Int.repr 2)))
        SEP(`(data_at Ews tint (repinj tint (Int.add (Int.add Int.zero Int.one) Int.one)) ctr);`(data_at Ews (tptr tint) ctr addof_ctr)).