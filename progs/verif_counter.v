Require Import floyd.proofauto.
Load counter.

Instance CompSpecs : compspecs.
Proof. make_compspecs prog. Defined.  

Local Open Scope logic.

Definition t_struct_zero := Tstruct _zero noattr.
Definition t_struct_ctr := Tstruct _ctr noattr.

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

Definition main_spec :=
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

Definition Vprog : varspecs := (_ctr, tptr tint)::(_zero,tint)::nil.

Definition Gprog : funspecs := 
  reset_spec::incr_spec::read_spec::main_spec::nil.

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

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
 start_function.
 name ctr_ _ctr.
 name ctr0_ _ctr0.
 name t_ _t.
 forward_call' (z, addof_ctr, ctr).
 forward_call' (Int.zero, addof_ctr, ctr).
 forward_call' ((Int.add Int.zero Int.one), addof_ctr, ctr).
 forward_call' ((Int.add (Int.add Int.zero Int.one) Int.one), addof_ctr, ctr) r0.
 forward.
Qed.

Existing Instance NullExtension.Espec.

Lemma all_funcs_correct:
  semax_func Vprog Gprog (prog_funct prog) Gprog.
Proof.
unfold Gprog, prog, prog_funct; simpl.
semax_func_skipn.
semax_func_cons body_reset.
semax_func_cons body_incr.
semax_func_cons body_read.
semax_func_cons body_main.
apply semax_func_nil.
Qed.

