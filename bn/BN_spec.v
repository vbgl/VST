Require Import floyd.proofauto.
Require Import Coqlib.
Require Import Integers.
Require Import List. Import ListNotations.
Local Open Scope logic.

Require Import sha.pure_lemmas.
Require Import sha.common_lemmas.

Require Import bn.minibn.
Require Import BN_repr.

(******************* From verif_queue etc ************************)

Definition mallocN_spec :=
 DECLARE _mallocN
  WITH n: int
  PRE [ 1%positive OF tint]
     PROP (4 <= Int.signed n) 
     LOCAL (temp 1%positive (Vint n))
     SEP ()
  POST [ tptr tvoid ] `(memory_block Tsh n) retval.

(***********************From spec_sha**************************)
(*
Definition memcpy_spec :=
  DECLARE _memcpy
   WITH sh : share*share, p: val, q: val, n: Z, contents: list int 
   PRE [ 1%positive OF tptr tvoid, 2%positive OF tptr tvoid, 3%positive OF tuint ]
       PROP (writable_share (snd sh); 0 <= n <= Int.max_unsigned)
       LOCAL (temp 1%positive p; temp 2%positive q; temp 3%positive (Vint (Int.repr n)))
       SEP (`(data_at (fst sh) (tarray tuchar n) (map Vint contents) q);
              `(memory_block (snd sh) (Int.repr n) p))
    POST [ tptr tvoid ]
         local (`(eq p) retval) &&
       (`(data_at (fst sh) (tarray tuchar n) (map Vint contents) q) *
        `(data_at (snd sh) (tarray tuchar n) (map Vint contents) p)).
*)
(***********************From spec_hmac*************************)

Record TREP := mkTrep { t: type; v: reptype t}.
Definition tp_of (T:TREP) : type.
  destruct T. apply t0. 
Defined.
Definition v_of (T:TREP) : reptype (tp_of T).
  destruct T. apply v0. 
Defined.

Definition memcpy_spec_data_at :=
  DECLARE _memcpy
   WITH sh : share*share, p: val, q: val, T:TREP
   PRE [ 1%positive OF tptr tvoid, 2%positive OF tptr tvoid, 3%positive OF tuint ]
       PROP (writable_share (snd sh); 0 <= sizeof  (tp_of T) <= Int.max_unsigned)
       LOCAL (`(eq p) (eval_id 1%positive); `(eq q) (eval_id 2%positive);
                    `(eq (Vint (Int.repr (sizeof (tp_of T))))) (eval_id 3%positive))
       SEP (`(data_at (fst sh)  (tp_of T) (v_of T) q);
              `(memory_block (snd sh) (Int.repr (sizeof  (tp_of T))) p))
    POST [ tptr tvoid ]
         local (`(eq p) retval) &&
       (`(data_at (snd sh) (tp_of T) (v_of T) p) *`(data_at (fst sh) (tp_of T) (v_of T) q)).

(******************************************************************)

Definition bn_new: bnabs:= BNabs nil 0 0 false Int.zero.

Definition bn_wexpand (A:bnabs) (w:int) : bnabs :=
  match A with BNabs chun t dm ng fl =>
    match nat_compare (Z.to_nat (Int.unsigned w)) dm with
      Gt => BNabs chun t (Z.to_nat (Int.unsigned w)) ng fl
    | _ => A
  end
  end.

Definition bn_wexpand_spec :=
  DECLARE _bn_wexpand
   WITH b:val, B:bnabs, w:int
   PRE [_bn OF tptr t_struct_bignum_st, _words OF tuint]
       PROP ( Int.unsigned w < 16777215 )
       LOCAL (temp _bn b; temp _words (Vint w))
       SEP (`(bnstate_ B b))
    POST [ tptr t_struct_bignum_st ] `(bnstate_ (bn_wexpand B w)) retval.
Parameter myZ1:Z.

Lemma body_bn_wexpand: semax_body nil (mallocN_spec ::memcpy_spec_data_at::nil)
      f_bn_wexpand bn_wexpand_spec.
Proof.
start_function.
name a _a.
name a' _a'.
unfold bnstate_; normalize. intros [d [top [dsize [neg flags]]]].
destruct B as [DATA TOP DSIZE NEG FLAGS].
unfold bn_relate; simpl. normalize.
intros topN; normalize. intros dsizeN; normalize. intros dsN; normalize.
(*unfold chunks_relate. normalize. intros TL. normalize.*)
remember
  (PROP  (Z.of_nat dsizeN < Int.unsigned w)
   LOCAL  (temp _bn b; temp _words (Vint w))
   SEP  (`(chunks_relate dsizeN DATA d);
   `(data_at Tsh t_struct_bignum_st (d, (top, (dsize, (neg, flags)))) b))) as PST.

forward_if PST.
 subst. simpl. intros rho. entailer. simpl.  admit.

forward. forward. entailer. (*solves the goal but why?*)
  (* unfold POSTCONDITION, abbreviate. subst; simpl. intros rho. entailer.*)

subst PST; normalize.
remember
  (PROP  ()
   LOCAL  (temp _bn b; temp _words (Vint w))
   SEP  (`(chunks_relate dsizeN DATA d);
   `(data_at Tsh t_struct_bignum_st (d, (top, (dsize, (neg, flags)))) b))) as PST.
rewrite HeqPST.
forward_if PST.
  forward. rewrite mul_repr in H7. simpl in H7.
   rewrite Int.divs_pow2 with (logn:=Int.repr 7) in H7; try reflexivity.
   unfold Int.ltu in H7.
   destruct (zlt (Int.unsigned (Int.shrx (Int.repr 2147483647) (Int.repr 7)))
           (Int.unsigned _id)). 2: discriminate.
    unfold Int.shrx, Int.shl, Int.divs, Z.quot in l. simpl in l.
    rewrite Int.unsigned_repr in l. omega.
    rewrite int_max_unsigned_eq. omega.

  forward. subst PST; simpl. intros rho. entailer.
    
subst PST; simpl.

remember
  (PROP  ()
   LOCAL  (temp _bn b; temp _words (Vint w))
   SEP  (`(chunks_relate dsizeN DATA d);
   `(data_at Tsh t_struct_bignum_st (d, (top, (dsize, (neg, flags)))) b))) as PST.

forward_if PST.
 subst. simpl. intros rho.  entailer. simpl.  admit.

forward. forward. entailer. 

subst PST; normalize.
assert (U: exists u, Int.mul (Int.repr 4) w = Int.repr u /\ 0 <= u <= Int.max_unsigned). admit. (*later*)
destruct U as [u [U UBND]].
forward_call (Int.repr u).
  entailer!.
  rewrite <- U; clear U. admit. (*later: exploit that 1<=w holds by H6*)
after_call. clear a'0.
forward.
remember
  (EX aval:val,
   PROP  ()
   LOCAL 
   (temp _a aval;
   temp _bn b; temp _words (Vint w))
   SEP  (`(memory_block Tsh (Int.repr u)) (eval_id _a);
   `(chunks_relate dsizeN DATA d);
   `(data_at Tsh t_struct_bignum_st (d, (top, (dsize, (neg, flags)))) b))) as PST.
forward_if PST.
  forward. rename _id0 into i. unfold isptr in Pa'. 
    destruct a'; simpl in *; try contradiction. inv H7.
  forward. subst PST; simpl. intros rho; entailer.
    remember (eval_id _a' rho) as aval.
    unfold isptr in H9. destruct aval; simpl in *; try contradiction.
    rewrite H2 in *. simpl in H1. 
    apply (exp_right (Vptr b0 i)). unfold temp. entailer. rewrite H2. cancel.
subst PST; normalize. apply extract_exists_pre. intros av.
unfold chunks_relate. normalize. intros TL. normalize.
rewrite <- H7 in *; clear H7.

(*replace (eval_id _a) with av, so that we can use memory_block_split;
  this was a bit more elegant before temp was introduced*)
apply semax_pre with (P':=
  (PROP  ()
   LOCAL  (temp _a av; temp _bn b; temp _words (Vint w))
   SEP 
   (`(data_at Tsh (tarray tuint (Z.of_nat (length (DATA ++ TL))))
        (map Vint (DATA ++ TL)) d);
   `(memory_block Tsh (Int.repr u) av);
   `(data_at Tsh t_struct_bignum_st (d, (top, (dsize, (neg, flags)))) b)))).
  entailer.

rewrite memory_block_isptr. normalize.
destruct av; simpl in *; try contradiction. clear H7. rename b0 into av.
assert (exists zz, u = (Z.of_nat (mult topN 4%nat)) + zz /\ 0 <= zz).
  assert (Int.unsigned (Int.mul (Int.repr 4) w) = Int.unsigned (Int.repr u)).
    rewrite U; trivial.
  rewrite Int.unsigned_repr in H7; trivial.
  subst u. exists (Zmult (Int.unsigned w - Z.of_nat topN) 4).
  rewrite Nat2Z.inj_mul. simpl.
  rewrite Z.mul_sub_distr_r, Zplus_minus.
  simpl. 
  specialize (mul_repr 4 (Int.unsigned w)).
  rewrite Int.repr_unsigned. intros IM; rewrite IM; clear IM.
   rewrite Z.mul_comm.
   rewrite Int.unsigned_repr. split; trivial. omega. 
   rewrite int_max_unsigned_eq. omega.
destruct H7 as [zz [ZZ ZZpos]]. subst u.
specialize (memory_block_split Tsh av (Int.unsigned i) (Z.of_nat (mult topN 4%nat)) zz).
rewrite Int.repr_unsigned. intros MBS.
rewrite MBS; trivial; clear MBS.
Focus 2. omega.
Focus 2. rewrite <-initialize.max_unsigned_modulus. omega.
normalize. unfold tarray. rewrite H2.
unfold_data_at 1%nat.
unfold field_at. simpl. normalize. SearchAbout array_at'. simpl. specify memcpy now on array_at'??
erewrite field_at_Tarray. 2: reflexivity. 2: apply JMeq.JMeq_refl.
SearchAbout array_at. unfold Tarray.
specialize split2_array_at0 TSh .
specialize (data_at_Tarray_split3 Tsh tuint). 
(Z.of_nat (dsN * 4)) noattr (Z.of_nat (topN * 4))).
 (*(Z.of_nat (topN * 4))*)
remember (mkTrep (tarray tuint myZ1) (map Vint (DATA ++ TL))) as W.

remember ((Tsh, Tsh), Vptr av i, d, W) as WIT.
(*remember ((Tsh, Tsh), Vptr av i, d, Z.of_nat mx, ch ++ TL) as WIT.*)
forward_call WIT.
 { assert (FR: Frame = [`(data_at Tsh t_struct_bignum_st (d, (top, (dsize, (neg, flags)))) b);
                        `(memory_block Tsh (Int.repr zz)
    (Vptr av (Int.repr (Int.unsigned i + Z.of_nat (mult topN 4%nat)))))]).
     subst Frame. reflexivity. 
   rewrite FR. clear FR Frame. 
   subst WIT. simpl. intros rho. entailer. simpl.
   destruct d; simpl in *; try contradiction.
   rewrite Z.max_comm. (* initialize.Zmax_Z_of_nat.*)
   apply andp_right.
   apply prop_right. admit. (*later*)
   cancel.  rewrite Z.max_comm, initialize.Zmax_Z_of_nat.
   erewrite (data_at_type_changable _ _ (tarray tuchar (Z.of_nat (length (ch ++ TL))))).
    apply derives_refl.


admit.

omega.
assert (exists zz, w4 = (Z.of_nat mx) + zz). admit.
destruct H6 as [zz ZZ]. subst w4.
specialize (memory_block_split Tsh av (Int.unsigned i) (Z.of_nat mx) zz).
rewrite Int.repr_unsigned; intros.
rewrite H6; clear H6.
normalize.
remember (mkTrep (tarray tuint (Z.of_nat mx)) (map Vint (ch ++ TL))) as W.

remember ((Tsh, Tsh), Vptr av i, d, W) as WIT.
(*remember ((Tsh, Tsh), Vptr av i, d, Z.of_nat mx, ch ++ TL) as WIT.*)
forward_call WIT.
 { assert (FR: Frame = [`(data_at Tsh t_struct_bignum_st (d, (t, (m, (n, f)))) b);
                        `(memory_block Tsh (Int.repr zz)
                          (Vptr av (Int.repr (Int.unsigned i + Z.of_nat mx))))]).
     subst Frame. reflexivity. 
   rewrite FR. clear FR Frame. 
   subst WIT. simpl. intros rho. entailer. simpl.
   destruct d; simpl in *; try contradiction.
   apply andp_right.
   apply prop_right. admit. (*later*)
   cancel.  rewrite Z.max_comm, initialize.Zmax_Z_of_nat.
   erewrite (data_at_type_changable _ _ (tarray tuchar (Z.of_nat (length (ch ++ TL))))).
    apply derives_refl.
   simpl. unfold tarray. simpl. unfold tuchar, tuint.
      rewrite Z.max_comm, initialize.Zmax_Z_of_nat.
      remember (Z.of_nat (length (ch ++ TL))) as l. SearchAbout Z.max 0.  ext. cancel. 
   instantiate (1:=nil). subst WIT; simpl.
remember ((Tsh,Tsh), 
frame_SEP 2.
remember (mkTrep (tarray tuint (4 * Z.of_nat mx)) (map Vint (ch ++ TL))) as W.
remember ((Tsh, Tsh), av, d, W) as WIT.
eapply semax_seq'.
forward_call WIT.
 { assert (FR: Frame = nil).  subst Frame. reflexivity. 
   rewrite FR. clear FR Frame. 
   subst WIT W. simpl. ; intros. entailer. simpl.
   destruct av; simpl in *; try contradiction.
   destruct d; simpl in *; try contradiction.
   apply andp_right.
   apply prop_right. split. admit. (*later*)
      rewrite Z.max_comm, initialize.Zmax_Z_of_nat.
      remember (Z.of_nat (length (ch ++ TL))) as l. SearchAbout Z.max 0.  ext. cancel. 
   instantiate (1:=nil). subst WIT; simpl.
remember ((Tsh,Tsh), 
frame_SEP 2.

 isubst PST; simpl. intros rho; entailer!.  normalize. simpl in H6. unfold is_pointer_or_null in TC1. 
    remember (force_val (sem_cast_neutral a')) as q.
    destruct q; try contradiction. subst; simpl in *.
unfold isptr in Pa'. destruct a'; simpl in *. inv Heqq.
      unfold typed_true in H6. simpl in H6.
       destruct TC1. unfold sem_cmp_pp in H6. SearchAbout typed_true tint sem_cmp_pp. 

   rewrite Int.mul_signed.
   assert (1 <= Int.unsigned w). omega.
   rewrite Int.mul_signed.
rewrite Int.signed_repr.
rewrite Int.signed_repr.
rewrite Int.signed_eq_unsigned. omega. unfold Int.max_signed. simpl. omega.
unfold Int.max_signed, Int.min_signed. simpl. omega.
unfold Int.max_signed, Int.min_signed. simpl. omega.
forward_seq.
forward_seq.
forward_call WIT.
  entailer!.

intros. simpl. intros rho. simpl.

 SearchAbout Int.shl Int.one. Int.shl. simpl in l.  rewrite ltu_repr in H7. shrx. Focus 2. unfold Int.is_power2. reflexivity. simpl. simpl.  unfold Int.divs in H7. SearchAbout rewrite div_repr in H7. SearchAbout Int.mul. unfold Int.mul in H7. simpl.  unfold chunks_relate.  SearchAbout Int.ltu. unfold chunks_relate. SearchAbout Int.divs. Int.mul.

SearchAbout temp.
unfold temp in H6.
unfold both_int in H4. unfold temp, liftx in *. simpl in *.
unfold sem_cast_neutral in H4.
SearchAbout typed_false.
   simpl in H4.
forward_seq.

Definition bn_new: bnabs:= BNabs nil 0 0 false Int.zero.

Definition bn_new_spec :=
  DECLARE _BN_new
   WITH u:unit
   PRE []
       PROP ()
       LOCAL ()
       SEP ()
    POST [ tptr t_struct_bignum_st ] `(bnstate_ bn_new) retval.

Lemma body_bn_new: semax_body nil (malloc_spec ::nil)
      f_BN_new bn_new_spec.
Proof.
start_function.
forward_seq.
forward_seq.
admit. (*forward_call (Int.repr 20).
     assert (XX1: (var_types Delta) ! _malloc = None) 
        by (reflexivity || fail 4 "The function-identifier " id " is not a global variable").
    assert (match (glob_specs Delta) ! _malloc with
               | Some (mk_funspec _ t _ _) => Some t
               | _ => None
               end = None);
     simpl.*)
forward_call (Int.repr 20).
apply seq_assoc.
apply seq_assoc. Check (Int.repr 20).
remember (Int.repr 20) as WIT.
forward_call WIT.
forward_call (Int.repr 20).
unfold bnstate_; normalize. intros av. normalize. intros bv. normalize.
forward.
  entailer. unfold bn_relate. destruct A as [d t dm n].
   destruct av as [d' [t' [dm' [n' X]]]]. simpl. unfold tops_relate. normalize.
forward.
  entailer. unfold bn_relate. destruct B as [d t dm n].
   destruct bv as [d' [t' [dm' [n' X]]]]. simpl. unfold tops_relate. normalize.
forward.
remember (PROP  ()
   LOCAL  (temp _btop (fst (snd bv)); temp _atop (fst (snd av));
   `(eq a) (eval_id _a); `(eq b) (eval_id _b))
   SEP  (`(bn_relate A av); `(data_at Tsh t_struct_bignum_st av a);
   `(bn_relate B bv); `(data_at Tsh t_struct_bignum_st bv b))) as PST.
forward_if PST.
  subst PST; normalize. 
  forward. simpl in *.
   apply andp_right.
     unfold bn_ucmp. simpl. 
     destruct A as [dA tA dmA nA]. destruct av as [dA' [tA' [dmA' [nA' XA]]]].
     destruct B as [dB tB dmB nB]. destruct bv as [dB' [tB' [dmB' [nB' XB]]]].
     simpl in *. unfold chunks_relate. normalize. admit.
  unfold bnstate_. normalize. apply (exp_right bv). normalize.
   apply (exp_right av). normalize.

forward. subst PST. entailer.

subst PST; normalize.
forward. entailer. unfold bn_relate. destruct A as [d t dm n].
   destruct av as [d' [t' [dm' [n' X]]]]. simpl. unfold chunks_relate. entailer.
forward. entailer. unfold bn_relate. destruct B as [d t dm n].
   destruct bv as [d' [t' [dm' [n' X]]]]. simpl. unfold chunks_relate. normalize.
   destruct A as [dA tA dmA nA].
   destruct av as [dA' [tA' [dmA' [nA' XA]]]]. simpl. unfold chunks_relate. entailer.
continue here
destruct A as [d t dm n].
   destruct av as [d' [t' [dm' [n' X]]]]. simpl. unfold chunks_relate. entailer.

 normalize.
forward.
  entailer. unfold bn_relate. destruct B as [d t dm n].
   destruct bv as [d' [t' [dm' [n' X]]]]. simpl. unfold tops_relate. normalize.
forward.
 unfold bnstate_. entailer.  normalize. unfold POSTCONDITION, abbreviate. 
  unfold bnstate_. entailer.
  (dB',
  (Vint (Int.repr (Z.of_nat (length dB))),
  (Vint (Int.repr (Z.of_nat dmB)), (nB', XB))))). entailer. 
  apply (exp_right  (dA',
  (Vint (Int.repr (Z.of_nat (length dA))),
  (Vint (Int.repr (Z.of_nat dmA)), (nA', XA))))). entailer.
  unfold bn_relate. entailer. unfold tops_relate. entailer.
destruct A as [dA tA dmA nA]. destruct av as [dA' [tA' [dmA' [nA' XA]]]].
destruct B as [dB tB dmB nB]. destruct bv as [dB' [tB' [dmB' [nB' XB]]]].
simpl. normalize. unfold tops_relate in *. subst tA' tB' dmA' dmB'.
simpl.
remember (Int.sub (Int.repr (Z.of_nat tA)) (Int.repr (Z.of_nat tB))) as i. 
remember ((PROP  ( i <> Int.zero)
   LOCAL  (temp _i (Vint i); temp _btop (Vint (Int.repr (Z.of_nat tB)));
   temp _atop (Vint (Int.repr (Z.of_nat tA))); `(eq a) (eval_id _a);
   `(eq b) (eval_id _b))
   SEP  (`(chunks_relate dA dA');
   `(data_at Tsh t_struct_bignum_st
       (dA',
       (Vint (Int.repr (Z.of_nat tA)),
       (Vint (Int.repr (Z.of_nat dmA)), (nA', XA)))) a);
   `(chunks_relate dB dB');
   `(data_at Tsh t_struct_bignum_st
       (dB',
       (Vint (Int.repr (Z.of_nat tB)),
       (Vint (Int.repr (Z.of_nat dmB)), (nB', XB)))) b)))) as PST.
forward_if PST.
  subst PST; normalize. 
  forward. simpl in *.
   apply andp_right.
     unfold bn_ucmp. simpl. unfold chunks_relate. admit.
  unfold bnstate_. normalize. apply (exp_right  (dB',
  (Vint (Int.repr (Z.of_nat (length dB))),
  (Vint (Int.repr (Z.of_nat dmB)), (nB', XB))))). entailer. 
  apply (exp_right  (dA',
  (Vint (Int.repr (Z.of_nat (length dA))),
  (Vint (Int.repr (Z.of_nat dmA)), (nA', XA))))). entailer.
  unfold bn_relate. entailer. unfold tops_relate. entailer.
normalize.
forward. entailer. rewrite H2, H3 in *. simpl in *. inv H1.
  apply (exp_right (Int.sub _id1 _id0)). entailer.
  destruct A as [dA tA dmA nA]. destruct av as [dA' [tA' [dmA' [nA' XA]]]].
  destruct B as [dB tB dmB nB]. destruct bv as [dB' [tB' [dmB' [nB' XB]]]].
  unfold bn_relate. entailer. simpl in *. subst. admit.

   temp _btop (fst (snd bv)); temp _atop (fst (snd av));
   `(eq a) (eval_id _a); `(eq (Vint i)) (eval_id _i); `(eq b) (eval_id _b))
   SEP  (`(bn_relate A av); `(data_at Tsh t_struct_bignum_st av a);
   `(bn_relate B bv); `(data_at Tsh t_struct_bignum_st bv b)))) as PST.
forward_if PST.
  subst; normalize. 
  forward. simpl in *. rewrite H1, H2 in *. simpl in *. inv H0.
   apply andp_right.
     unfold bn_relate. destruct A as [dA tA dmA nA].
     destruct av as [dA' [tA' [dmA' [nA' XA]]]]. destruct B as [dB tB dmB nB].
     destruct bv as [dB' [tB' [dmB' [nB' XB]]]]. entailer. simpl in *. subst.
     unfold bn_ucmp. simpl. unfold chunks_relate. admit.
  unfold bnstate_. normalize. apply (exp_right bv). entailer.
    apply (exp_right av). entailer.
normalize.
forward. entailer. rewrite H2, H3 in *. simpl in *. inv H1.
  apply (exp_right (Int.sub _id1 _id0)). entailer.
  destruct A as [dA tA dmA nA]. destruct av as [dA' [tA' [dmA' [nA' XA]]]].
  destruct B as [dB tB dmB nB]. destruct bv as [dB' [tB' [dmB' [nB' XB]]]].
  unfold bn_relate. entailer. simpl in *. subst. admit.

subst.

forward_seq.
subst. forward. apply extract_exists. exp_left. forward.
eapply semax_seq'.
ensure_normal_ret_assert;
 hoist_later_in_pre.
Print t_struct_bignum_st.
match goal with
| SE := @abbreviate type_id_env.type_id_env _ 
    |- semax ?Delta (|> (PROPx ?P (LOCALx ?Q (SEPx ?R)))) (Sset _ ?e) _ =>
 (* Super canonical load *)
    let e1 := fresh "e" in
    let efs := fresh "efs" in
    let tts := fresh "tts" in
      construct_nested_efield e e1 efs tts;

    let lr := fresh "lr" in
      pose (compute_lr e1 efs) as lr;
      vm_compute in lr;

    let HLE := fresh "H" in
    let p := fresh "p" in evar (p: val);
      match goal with
      | lr := LLLL |- _ => do_compute_lvalue Delta P Q R e1 p HLE
      | lr := RRRR |- _ => do_compute_expr Delta P Q R e1 p HLE
      end;

    let H_Denote := fresh "H" in
    let gfs := fresh "gfs" in
      solve_efield_denote Delta P Q R efs gfs H_Denote
end.
;

    let sh := fresh "sh" in evar (sh: share);
    let t_root := fresh "t_root" in evar (t_root: type);
    let gfs0 := fresh "gfs" in evar (gfs0: list gfield);
    let v := fresh "v" in evar (v: reptype (nested_field_type2 t_root gfs0));
    let n := fresh "n" in
    let H := fresh "H" in
    let H_LEGAL := fresh "H" in
    sc_new_instantiate SE P Q R R Delta e1 gfs tts lr p sh t_root gfs0 v n (0%nat) H H_LEGAL
end.
;
    
    let gfs1 := fresh "gfs" in
    let efs0 := fresh "efs" in
    let efs1 := fresh "efs" in
    let tts0 := fresh "tts" in
    let tts1 := fresh "tts" in
    let len := fresh "len" in
    pose ((length gfs - length gfs0)%nat) as len;
    simpl in len;
    match goal with
    | len := ?len' |- _ =>
      pose (firstn len' gfs) as gfs1;
      pose (skipn len' efs) as efs0;
      pose (firstn len' efs) as efs1;
      pose (skipn len' tts) as tts0;
      pose (firstn len' tts) as tts1
    end;
    clear len;
    unfold gfs, efs, tts in gfs0, gfs1, efs0, efs1, tts0, tts1;
    simpl firstn in gfs1, efs1, tts1;
    simpl skipn in gfs0, efs0, tts0;

    change gfs with (gfs1 ++ gfs0) in *;
    change efs with (efs1 ++ efs0) in *;
    change tts with (tts1 ++ tts0) in *;
    subst gfs efs tts p;

    let Heq := fresh "H" in
    match type of H with
    | (PROPx _ (LOCALx _ (SEPx (?R0 :: nil))) 
           |-- _) => assert (nth_error R n = Some R0) as Heq by reflexivity
    end;
    eapply (semax_SC_field_load Delta sh SE n) with (lr0 := lr) (t_root0 := t_root) (gfs2 := gfs0) (gfs3 := gfs1);
    [reflexivity | reflexivity | reflexivity
    | reflexivity | reflexivity | exact Heq | exact HLE | exact H_Denote 
    | exact H | reflexivity
    | try solve [entailer!]; try (clear Heq HLE H_Denote H H_LEGAL;
      subst e1 gfs0 gfs1 efs1 efs0 tts1 tts0 t_root v sh lr n; simpl app; simpl typeof)
    | solve_legal_nested_field_in_entailment; try clear Heq HLE H_Denote H H_LEGAL;
      subst e1 gfs0 gfs1 efs1 efs0 tts1 tts0 t_root v sh lr n]
end.


forward.
  entailer.

