Require Import floyd.proofauto.
Require Import Coqlib.
Require Import Integers.
Require Import List. Import ListNotations.
Local Open Scope logic.

Require Import sha.pure_lemmas.
Require Import sha.common_lemmas.

Require Import bn.minibn.
Require Import BN_repr.
Require Import minibn_cmp.

(*Mathematic def - version which traverses the chunks to be added later*)
Definition chunks_cmp (a b: list Chunk ) : int :=
  if zlt (chunks2Z a) (chunks2Z b) then Int.mone else
  if zle (chunks2Z a) (chunks2Z b) then Int.zero else Int.one.

Definition bn_ucmp (a b: bnabs ) : int := 
  chunks_cmp (bn_chunks a) (bn_chunks b).
 
Definition bn_ucmp_spec :=
  DECLARE _BN_ucmp
   WITH A:bnabs, B:bnabs, a: val, b: val
   PRE [ _a OF tptr t_struct_bignum_st, _b OF tptr t_struct_bignum_st]
       PROP ()
       LOCAL (`(eq a) (eval_id _a); `(eq b) (eval_id _b))
       SEP (`(bnstate_ A a); `(bnstate_ B b))
    POST [ tint ]
       PROP ()
       LOCAL (`(eq (Vint (bn_ucmp A B))) retval)
       SEP (`(bnstate_ A a); `(bnstate_ B b)).

Lemma body_bn_ucmp: semax_body nil nil
      f_BN_ucmp bn_ucmp_spec.
Proof.
start_function.
name a' _a.
name b' _b.
name i' _i.
(*name A' _A.
simpl_stackframe_of.*)
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

