Require Import Events. (*is needed for some definitions (loc_unmapped etc*)
Require Import Memory.
Require Import Coqlib.
Require Import Integers.
Require Import compcert.common.Values.
Require Import Maps.
Require Import Axioms.
Require Import Globalenvs.

Require Import sepcomp.mem_lemmas.
Require Import minisepcomp.mini_simulations.
Require Import minisepcomp.mini_simulations_lemmas.
Require Import minisepcomp.mem_interpolation_defs.
Require Import minisepcomp.BuiltinEffects.

Definition mem_add_acc (j23 :meminj) (m1 m1' m2 : mem) (L2 B:block -> bool) :=
  fun b2 ofs2 k =>
       if valid_block_dec m2 b2 then 
         if B b2 then PMap.get b2 m2.(Mem.mem_access) ofs2 k else
           if L2 b2 then
               if Mem.perm_dec m1 b2 ofs2 Max Nonempty  
               then PMap.get b2 m1'.(Mem.mem_access) ofs2 k
               else PMap.get b2 m2.(Mem.mem_access) ofs2 k
           else if Mem.perm_dec m1 b2 ofs2 Max Nonempty 
                then PMap.get b2 m1'.(Mem.mem_access) ofs2 k
                else None (*match j23 b2 with 
                                None => PMap.get b2 m2.(Mem.mem_access) ofs2 k
                              | Some (b3,d3) =>  None 
                            end*)
               
       else PMap.get b2 m1'.(Mem.mem_access) ofs2 k.

Definition mem_add_cont (j23 :meminj) (m1 m1' m2 : mem) (L2 B:block -> bool) :=
fun b2 ofs2 =>
  if valid_block_dec m2 b2 then 
    if B b2 then ZMap.get ofs2 (m2.(Mem.mem_contents) !! b2) else
    if L2 b2 then
          match j23 b2 with 
                 None => ZMap.get ofs2 (m2.(Mem.mem_contents) !! b2)
               | Some _ => if Mem.perm_dec m1 b2 ofs2 Max Nonempty 
                     then ZMap.get ofs2 (PMap.get b2 m1'.(Mem.mem_contents))
                     else ZMap.get ofs2 ( m2.(Mem.mem_contents) !! b2)
          end
      else if Mem.perm_dec m1 b2 ofs2 Max Nonempty 
        then ZMap.get ofs2 (PMap.get b2 m1'.(Mem.mem_contents))
        else match j23 b2 with 
                None =>  ZMap.get ofs2 ( m2.(Mem.mem_contents) !! b2)
              | Some (b3,d3) =>  Undef 
            end
  else
      if Mem.perm_dec m1' b2 ofs2 Max Nonempty
      then ZMap.get ofs2 (PMap.get b2 m1'.(Mem.mem_contents))
      else ZMap.get ofs2 (fst (Mem.mem_contents m2)).

Lemma interpolation_EI_exists:
  forall (j23 :meminj) (m1 m1' m2: mem) L2 B,
    exists m2', (forall b ofs, ZMap.get ofs (Mem.mem_contents m2') !! b = 
                                   mem_add_cont j23 m1 m1' m2 L2 B b ofs) /\
                    (forall b, (Mem.mem_access m2') !! b = 
                               mem_add_acc j23 m1 m1' m2 L2 B b) /\  
                    (Mem.nextblock m2' = Mem.nextblock m1').
Admitted. (*TODO: follow interpolation_memory construction*)

Section Interpolation_EI.
  Variable F2 V2: Type.
  Variable g2 : Genv.t F2 V2.
  Variable F3 V3: Type.
  Variable g3 : Genv.t F3 V3.
  Variable m1 m2 m1' m3 m3':mem.
  Variable j j': meminj.
  Variable L1 L3 B1 B2 B3: block -> bool.
  Variable Ext12: Mem.extends m1 m2.
  Variable Fwd1: mem_forward m1 m1'.
  Variable Inj23: Mem.inject j m2 m3.
  Variable Fwd3: mem_forward m3 m3'.
  Variable Inj13': Mem.inject j' m1' m3'.
  Variable UnchSrc : Mem.unchanged_on (fun b1 _ => L1 b1 = true /\ j b1 = None) m1 m1'.
  Variable UnchTgt : Mem.unchanged_on (o_o_reach j L3 m1) m3 m3'.
  Variable INC : mini_extern_incr j j' L1 L3.
  Variable GSep : globals_separate (*g2*)m2 g3 j j'.
  Variable MV : meminj_valid j' L1 m1' L3 m3'.
  Variable WDj : forall (b1 b2 : block) (d : Z), j b1 = Some (b2, d) -> L1 b1 = L3 b2.
  Variable HB23: forall b2 b3 d, j b2 = Some (b3, d) -> B2 b2 = true -> B3 b3 = true.
  Variable HB12: forall b2, B2 b2 = true -> B1 b2 = true.
  Variable HB1L1: forall b1, B1 b1 = true -> L1 b1 = false.
  Variable RDOnly_fwd1: RDOnly_fwd m1 m1' B1.
  Variable RDOnly_fwd3: RDOnly_fwd m3 m3' B3.

(*  Variable RDOs_are_globals3: forall b3, B3 b3 = true -> isGlobalBlock g3 b3 = true.*)
  Variable RDOs_are_globals3: forall b3, B3 b3 = true -> Plt b3 (Genv.genv_next g3).

Lemma NB: Mem.nextblock m1 = Mem.nextblock m2. apply Ext12. Qed.

Lemma VB b: Mem.valid_block m1 b = Mem.valid_block m2 b.
Proof. unfold Mem.valid_block. rewrite NB; trivial. Qed.

Lemma interp_EI: exists m2',
  Mem.extends m1' m2' /\
  mem_forward m2 m2' /\
  Mem.inject j' m2' m3' /\
  RDOnly_fwd m2 m2' B2 /\
  Mem.unchanged_on (o_o_reach (Mem.flat_inj (Mem.nextblock m1)) L1 m1) m2 m2' /\
  Mem.unchanged_on (fun (b1 : block) (_ : Z) => L1 b1 = true /\ j b1 = None) m2 m2'.
Proof. 
destruct (interpolation_EI_exists j m1 m1' m2 L1 B2) as [m2' [CONT [ACCESS NB']]].
exists m2'.
assert (VB' : forall b : block, Mem.valid_block m1' b = Mem.valid_block m2' b).
{ intros; unfold Mem.valid_block. rewrite NB'; trivial. }

assert (Inj13:= Mem.extends_inject_compose _ _ _ _ Ext12 Inj23).
assert (MMU_LU: Mem.unchanged_on (fun b1 _ => L1 b1 = true /\ j b1 = None) m2 m2' ).
{ split. 
  + rewrite NB', <- (Mem.mext_next _ _ Ext12). eapply mem_forward_nextblock. trivial. 
  + intros. destruct H as [Lb Jb].
    unfold Mem.perm at 2. rewrite ACCESS. unfold mem_add_acc. clear CONT ACCESS.
    destruct (valid_block_dec m2 b); try contradiction. rewrite Lb.
    remember (B2 b) as q; destruct q. split; auto.
    remember (Mem.perm_dec m1 b ofs Max Nonempty) as w.
    destruct w. 2: split; eauto.
    split; intros. 
    - apply UnchSrc. split; trivial. rewrite Mem.valid_block_extends; eassumption.
      destruct (Mem.mext_perm_inv _ _ Ext12 _ _ _ _ H). trivial. contradiction.
    - apply UnchSrc in H. 2: split; trivial. 2: rewrite Mem.valid_block_extends; eassumption.
      eapply Mem.perm_extends; eassumption.
  + intros. destruct H as [Lb Jb]. rewrite CONT; clear CONT. unfold mem_add_cont.
    specialize (Mem.perm_valid_block _ _ _ _ _ H0); intros vb2.
    destruct (valid_block_dec m2 b); try contradiction. rewrite <- VB in v.
    rewrite Jb, Lb.
    remember (B2 b) as q; symmetry in Heqq.
    destruct q. { apply HB12 in Heqq. apply HB1L1 in Heqq. congruence. }
    (*destruct (Mem.perm_dec m1 b ofs Max Nonempty); trivial.*) trivial. }
assert (Fwd2: mem_forward m2 m2').
{ split; intros. 
  + (*valid_block*) apply (Mem.valid_block_extends _ _ b Ext12) in H. 
        apply Fwd1 in H. destruct H as[H _]. rewrite <- VB'. apply H. 
  + (*max*)
    unfold Mem.perm in H0. rewrite ACCESS in H0; clear ACCESS CONT. unfold mem_add_acc in H0.
    destruct (valid_block_dec m2 b); try contradiction.
    remember (B2 b) as q; symmetry in Heqq.
    destruct q; trivial.
    remember (L1 b) as w; symmetry in Heqw.
    destruct w.
    { remember (Mem.perm_dec m1 b ofs Max Nonempty) as t.
      destruct t;  trivial. clear Heqt.
      eapply Mem.perm_extends. eassumption.
      apply Fwd1; trivial. rewrite VB; trivial. }
    remember (Mem.perm_dec m1 b ofs Max Nonempty) as t.
    destruct t.
    { clear Heqt. 
      eapply Mem.perm_extends. eassumption.
      apply Fwd1; trivial. rewrite VB; trivial. }
    (*destruct (j b); trivial. destruct p0; contradiction.*) contradiction. }
assert (MMU_LOOR: Mem.unchanged_on (o_o_reach (Mem.flat_inj (Mem.nextblock m1)) L1 m1) m2 m2'). 
{ split.
  + apply MMU_LU.
  + intros. destruct H as [Lb Pb].
    unfold Mem.perm at 2. rewrite ACCESS; clear ACCESS CONT. unfold mem_add_acc.
    destruct (valid_block_dec m2 b); try contradiction.
    rewrite Lb. rewrite <- VB in H0. specialize (Pb b 0). rewrite Zminus_0_r, flatinj_I in Pb; trivial.
    remember (B2 b) as q; symmetry in Heqq.
    destruct q. { split; auto. }
    remember (Mem.perm_dec m1 b ofs Max Nonempty) as t.
    destruct t. 
    { elim Pb; trivial. }
    { split; auto. }
  + intros. destruct H as [Lb Pb]. rewrite CONT; clear CONT. unfold mem_add_cont.
    destruct (valid_block_dec m2 b). 2: solve [elim n; eapply Mem.perm_valid_block; eassumption].
    rewrite Lb.
    destruct (B2 b); trivial.
    remember (Mem.perm_dec m1 b ofs Max Nonempty) as w.
    destruct w; trivial.
    rewrite <- VB in v.
    specialize (Pb b 0). rewrite flatinj_I, Zminus_0_r in Pb; trivial.
    elim Pb; trivial.
    destruct (j b); trivial. }
assert (Ext12':  Mem.extends m1' m2').
{ split. 
  + (*nextblock*) rewrite NB'; trivial. 
  + (*mem_inj*)
     assert (Perm12': forall b ofs k p, Mem.perm m1' b ofs k p -> 
                                        Mem.perm m2' b ofs k p).
     { intros.
       unfold Mem.perm; rewrite ACCESS; clear ACCESS CONT. unfold mem_add_acc.
       destruct (valid_block_dec m2 b); trivial.
       remember (B2 b) as q; symmetry in Heqq; destruct q.
       - specialize (RDOnly_fwd1 _ (HB12 _ Heqq)). red in RDOnly_fwd1.
         eapply Mem.perm_extends. eassumption. 
         apply HB12 in Heqq. admit. (*RDO SRC*)
       - remember (L1 b) as w; symmetry in Heqw; destruct w.
         * remember (Mem.perm_dec m1 b ofs Max Nonempty) as t.
           destruct t; [ apply H | ].
           elim n. apply Fwd1. rewrite VB; trivial.
           eapply Mem.perm_implies. eapply Mem.perm_max. apply H. constructor.
         * remember (Mem.perm_dec m1 b ofs Max Nonempty) as t.
           destruct t; [ apply H | ].
           elim n. apply Fwd1. rewrite VB; trivial.
           eapply Mem.perm_implies. eapply Mem.perm_max. apply H. constructor. }
     split.  
       - (*mi_perm*) intros. inv H. rewrite Zplus_0_r. 
                     apply (Perm12' _ _ _ _ H0). 
       - (*mi_align*) intros. inv H. apply Z.divide_0_r. 
       - (*mi_memval *) intros. inv H. rewrite Zplus_0_r.
         rewrite CONT; clear CONT. unfold mem_add_cont.
         destruct (valid_block_dec m2 b2).
         { remember (B2 b2) as q; symmetry in Heqq; destruct q.
           + specialize (RDOnly_fwd1 _ (HB12 _ Heqq)). red in RDOnly_fwd1.
             assert (ZZ: ZMap.get ofs (Mem.mem_contents m1') !! b2 = ZMap.get ofs (Mem.mem_contents m1) !! b2).
             { apply HB12 in Heqq. admit. (*RDO in Src*) }
             rewrite ZZ. specialize (Mem.mi_memval _  _ _ (Mem.mext_inj _ _ Ext12) b2 ofs _ _ (eq_refl _)). intros P.
             rewrite Zplus_0_r in P. apply P; clear P.
             rewrite <- VB in v. apply HB12 in Heqq. admit. (*RDO in Src*) 
           + remember (L1 b2) as w; symmetry in Heqw; destruct w.
             - remember (Mem.perm_dec m1 b2 ofs Max Nonempty) as t; destruct t.
               * clear Heqt. remember (j b2) as s; symmetry in Heqs; destruct s.
                 ++ apply memval_inject_id_refl.
                 ++ rewrite <- VB in v. destruct UnchSrc as [_ USPerm USVal].
                    apply USPerm in H0; trivial. 2: split; trivial.
                    rewrite USVal; trivial. 2: split; trivial.
                    specialize (Mem.mi_memval _  _ _ (Mem.mext_inj _ _ Ext12) b2 ofs _ _ (eq_refl _)). intros P.
                    rewrite Zplus_0_r in P. apply P; trivial.
               * rewrite <- VB in v. elim n. apply Fwd1; trivial.
                 eapply Mem.perm_max. eapply Mem.perm_implies. apply H0. constructor.
             - remember (Mem.perm_dec m1 b2 ofs Max Nonempty) as t; destruct t.
               * apply memval_inject_id_refl.
               * rewrite <- VB in v. elim n. apply Fwd1; trivial.
                 eapply Mem.perm_max. eapply Mem.perm_implies. apply H0. constructor. }
         { remember (Mem.perm_dec m1' b2 ofs Max Nonempty) as t; destruct t.
           + apply memval_inject_id_refl.
           + elim n0. eapply Mem.perm_max. eapply Mem.perm_implies. apply H0. constructor. } 
  + (*mi_perm_inv *)  
         intros. unfold Mem.perm in H. rewrite ACCESS in H; clear ACCESS CONT. unfold mem_add_acc in H.
         destruct (valid_block_dec m2 b).
         { remember (B2 b) as q; symmetry in Heqq; destruct q.
           + destruct (Mem.mext_perm_inv _ _ Ext12 _ _ _ _ H).
             - left. apply HB12 in Heqq. admit. (*RDO in Src*) 
             - right. rewrite <- VB in v. intros N. apply H0. apply Fwd1; trivial.
           + remember (L1 b) as w; symmetry in Heqw; destruct w.
             - remember (Mem.perm_dec m1 b ofs Max Nonempty) as t; destruct t.
               * left; trivial.
               * right. rewrite <- VB in v. intros N. apply n. apply Fwd1; trivial.
             - remember (Mem.perm_dec m1 b ofs Max Nonempty) as t; destruct t.
               * left; trivial.
               * right. rewrite <- VB in v. intros N. apply n. apply Fwd1; trivial. }
         { left; trivial. } } 
assert (Inj23': Mem.inject j' m2' m3').
{ destruct INC as [INC1 INC2].
  assert (MI: Mem.mem_inj j' m2' m3').
  { assert (MiPerm: forall b1 b2 delta ofs k p,  j' b1 = Some (b2, delta) ->
                       Mem.perm m2' b1 ofs k p -> 
                       Mem.perm m3' b2 (ofs + delta) k p).
    + intros b2 b3; intros.
      assert (NP: Mem.perm m2' b2 ofs Max Nonempty).
      { eapply Mem.perm_max. eapply Mem.perm_implies. apply H0. constructor. }
      unfold Mem.perm in H0; rewrite ACCESS in H0; unfold mem_add_acc in H0.
      unfold Mem.perm in NP; rewrite ACCESS in NP; unfold mem_add_acc in NP.
      destruct (valid_block_dec m2 b2).
      { assert (Val1: Mem.valid_block m1 b2) by (rewrite VB; trivial).
        remember (B2 b2) as q; symmetry in Heqq; destruct q.
        + remember (j b2) as w; symmetry in Heqw; destruct w.
          - destruct p0. specialize (INC1 _ _ _ Heqw). rewrite INC1 in H; inv H.
            apply (HB23 _ _ _ Heqw) in Heqq.
            assert (P3: Mem.perm m3 b3 (ofs + delta) k p) by (eapply Inj23; eassumption).
            admit. (*RDO Tgt*) 
          - admit. (*readonly blocks are mapped*)
        + remember (L1 b2) as w; symmetry in Heqw; destruct w.
          - remember (Mem.perm_dec m1 b2 ofs Max Nonempty) as  t; destruct t.
            * clear Heqt. eapply Inj13'; eassumption.
            * remember (j b2) as s; symmetry in Heqs; destruct s.
              ++ destruct p0. specialize (INC1 _ _ _ Heqs). rewrite INC1 in H; inv H.
                 eapply UnchTgt.
                 -- split. rewrite <- (WDj _ _ _ Heqs); trivial.
                    intros. intros N. 
                    destruct (eq_block b1 b2).
                    ** subst. rewrite J in Heqs; inv Heqs.
                       assert (A:ofs + delta - delta = ofs) by omega.
                       rewrite A in N; contradiction.
                    ** apply (Mem.perm_extends _ _ _ _ _ _ Ext12) in N.
                       destruct (Mem.mi_no_overlap _ _ _ Inj23 _ _ _ _ _ _ _ _ n0 J Heqs N NP).
                       congruence. omega.
                 -- eapply Inj23; eassumption.
                 -- eapply Inj23; eassumption.
              ++ destruct (INC2 _ _ _ Heqs H). congruence.
          - remember (Mem.perm_dec m1 b2 ofs Max Nonempty) as t; destruct t.
            * eapply Inj13'; eassumption.
            * contradiction. (* remember (j b2) as z; symmetry in Heqz; destruct z.
                ++ destruct p0; contradiction.
                ++ destruct (Mem.perm_dec m1' b2 ofs k p).
                   -- eapply Inj13'; eassumption.
                   --   need "left side" of old inject_seprated?*)
      }
      { eapply Inj13'; eassumption. }
   + split; trivial. 
     - intros b2 b3; intros. red in H0. unfold Mem.perm in H0. rewrite ACCESS in H0. unfold mem_add_acc in H0.
       destruct (valid_block_dec m2 b2).
       { assert (Val1: Mem.valid_block m1 b2) by (rewrite VB; trivial).
         remember (B2 b2) as q; symmetry in Heqq; destruct q.
         + remember (j b2) as w; symmetry in Heqw; destruct w.
          - destruct p0. specialize (INC1 _ _ _ Heqw). rewrite INC1 in H; inv H.
            apply (HB23 _ _ _ Heqw) in Heqq.
            eapply Inj23. eassumption. red; intros. apply H0. apply H.
          - admit. (*readonly blocks are mapped*)
         + remember (L1 b2) as w; symmetry in Heqw; destruct w.
           - remember (j b2) as s; symmetry in Heqs; destruct s.
              ++ destruct p0. specialize (INC1 _ _ _ Heqs). rewrite INC1 in H; inv H.
                 eapply Inj23. eassumption.
                 red; intros. specialize (H0 _ H).
                 destruct (Mem.perm_dec m1 b2 ofs0 Max Nonempty).
                 -- eapply Mem.perm_extends; eassumption.
                 -- eapply Mem.perm_implies. eassumption. constructor.
              ++ destruct (INC2 _ _ _ Heqs H). congruence.
           - eapply Inj13'. eassumption.
                 red; intros. specialize (H0 _ H1).
                 destruct (Mem.perm_dec m1 b2 ofs0 Max Nonempty). apply H0.
                 contradiction.
(*                 -- eapply Mem.perm_extends; eassumption.
                 -- contradiction.remember (j b2) as s; symmetry in Heqs; destruct s.
              ++ destruct p0. specialize (INC1 _ _ _ Heqs). rewrite INC1 in H; inv H.
                 eapply Inj23. eassumption.
                 red; intros. specialize (H0 _ H).
                 destruct (Mem.perm_dec m1 b2 ofs0 Max Nonempty).
                 -- eapply Mem.perm_extends; eassumption.
                 -- contradiction.
              ++  need "left side" of old inject_seprated?*) }
       { eapply Inj13'; eassumption. }
     - intros b2 ofs b3; intros.
       unfold Mem.perm in H0; rewrite ACCESS in H0. unfold mem_add_acc in H0.
       rewrite CONT; clear CONT ACCESS. unfold mem_add_cont.
       destruct (valid_block_dec m2 b2).
       { assert (Val1: Mem.valid_block m1 b2) by (rewrite VB; trivial).
         remember (B2 b2) as q; symmetry in Heqq; destruct q.
         + remember (j b2) as w; symmetry in Heqw; destruct w.
          - destruct p. rewrite (INC1 _ _ _ Heqw) in H; inv H.
            apply (HB23 _ _ _ Heqw) in Heqq.
            assert (RD3: ZMap.get (ofs + delta) (Mem.mem_contents m3') !! b3 =
                    ZMap.get (ofs + delta) (Mem.mem_contents m3) !! b3). admit. (*RDO TGT*)
            rewrite RD3; clear RD3.
            eapply memval_inject_incr. 
            * eapply Inj23; eassumption.
            * assumption. 
          - admit. (*readonly blocks are mapped*)  
         + remember (L1 b2) as w; symmetry in Heqw; destruct w.
           - destruct (Mem.perm_dec m1 b2 ofs Max Nonempty).
             * remember (j b2) as s; symmetry in Heqs; destruct s.
               ++ destruct p0. apply Inj13'; eassumption.
               ++ destruct (INC2 _ _ _ Heqs H). congruence.
             * remember (j b2) as s; symmetry in Heqs; destruct s.
               ++ destruct p. rewrite (INC1 _ _ _ Heqs) in H; inv H.
                  destruct UnchTgt. rewrite unchanged_on_contents.
                    eapply memval_inject_incr; try eassumption.
                    apply Inj23; eassumption.
                    split. rewrite <- (WDj _ _ _ Heqs); trivial.
                    intros. intros N.
                    destruct (eq_block b1 b2); subst.
                    -- rewrite J in Heqs; inv Heqs.
                       assert (A: ofs + delta - delta = ofs) by omega.
                       rewrite A in *. contradiction.
                    -- destruct (Mem.mi_no_overlap j _ _ Inj23 b1 b3 delta0 b2 b3 delta (ofs + delta - delta0) ofs); trivial.
                         eapply Mem.perm_extends; eassumption.
                         eapply Mem.perm_max. eapply Mem.perm_implies. eassumption. constructor.
                       congruence. omega.
                   -- eapply Inj23; eassumption.
               ++ destruct (INC2 _ _ _ Heqs H). congruence.
           - destruct (Mem.perm_dec m1 b2 ofs Max Nonempty); try contradiction.
             eapply Inj13'; eassumption. }
       { destruct (Mem.perm_dec m1' b2 ofs Max Nonempty).
             eapply Inj13'; eassumption. 
         elim n0. eapply Mem.perm_max. eapply Mem.perm_implies. eassumption. constructor. } }
   split; trivial; try eapply Inj13'.
   + intros. apply Inj13'. intros N. rewrite VB' in N. apply (H N).
   + red; intros. 
     unfold Mem.perm in H2. rewrite ACCESS in H2. unfold mem_add_acc in H2. 
     unfold Mem.perm in H3. rewrite ACCESS in H3. unfold mem_add_acc in H3.
     clear ACCESS CONT.
     remember (j b1) as Jb1; symmetry in HeqJb1; destruct Jb1.
     - destruct p. assert (jj_b1 := INC1 _ _ _ HeqJb1). rewrite H0 in jj_b1; inv jj_b1.
       destruct (valid_block_dec m2 b1).
       Focus 2. elim n. eapply Mem.valid_block_inject_1. apply HeqJb1. eassumption.
       remember (j b2) as Jb2; symmetry in HeqJb2; destruct Jb2.
       * destruct p. assert (jj_b2 := INC1 _ _ _ HeqJb2). rewrite H1 in jj_b2; inv jj_b2.
         destruct (valid_block_dec m2 b2).
         Focus 2. elim n. eapply Mem.valid_block_inject_1. apply HeqJb2. eassumption.
         remember (B2 b1) as q1; symmetry in Heqq1; destruct q1; 
         remember (B2 b2) as q2; symmetry in Heqq2; destruct q2. 
         ++ eapply Inj23; eassumption.
         ++ remember (L1 b2) as w2; symmetry in Heqw2; destruct w2.
            -- destruct (Mem.perm_dec m1 b2 ofs2 Max Nonempty).
               ** eapply Inj23; try eassumption. eapply Mem.perm_extends; eassumption.
               ** eapply Inj23; try eassumption.
            -- destruct (Mem.perm_dec m1 b2 ofs2 Max Nonempty); try contradiction.
               eapply Inj23; try eassumption. eapply Mem.perm_extends; eassumption.
         ++ remember (L1 b1) as w1; symmetry in Heqw1; destruct w1.
            -- destruct (Mem.perm_dec m1 b1 ofs1 Max Nonempty).
               ** eapply Inj23; try eassumption. eapply Mem.perm_extends; eassumption.
               ** eapply Inj23; try eassumption.
            -- destruct (Mem.perm_dec m1 b1 ofs1 Max Nonempty); try contradiction.
               eapply Inj23; try eassumption. eapply Mem.perm_extends; eassumption.
         ++ remember (L1 b1) as w1; symmetry in Heqw1; destruct w1;
            remember (L1 b2) as w2; symmetry in Heqw2; destruct w2.
            -- destruct (Mem.perm_dec m1 b1 ofs1 Max Nonempty);
               destruct (Mem.perm_dec m1 b2 ofs2 Max Nonempty).
               ** eapply Inj23; try eassumption. eapply Mem.perm_extends; eassumption. eapply Mem.perm_extends; eassumption.
               ** eapply Inj23; try eassumption. eapply Mem.perm_extends; eassumption.
               ** eapply Inj23; try eassumption. eapply Mem.perm_extends; eassumption.
               ** eapply Inj23; try eassumption.
            -- destruct (Mem.perm_dec m1 b1 ofs1 Max Nonempty); 
               destruct (Mem.perm_dec m1 b2 ofs2 Max Nonempty); try contradiction.
               ** eapply Inj23; try eassumption. eapply Mem.perm_extends; eassumption. eapply Mem.perm_extends; eassumption.
               ** eapply Inj23; try eassumption. eapply Mem.perm_extends; eassumption.
            -- destruct (Mem.perm_dec m1 b1 ofs1 Max Nonempty); 
               destruct (Mem.perm_dec m1 b2 ofs2 Max Nonempty); try contradiction.
               ** eapply Inj23; try eassumption. eapply Mem.perm_extends; eassumption. eapply Mem.perm_extends; eassumption.
               ** eapply Inj23; try eassumption. eapply Mem.perm_extends; eassumption.
            -- destruct (Mem.perm_dec m1 b1 ofs1 Max Nonempty); 
               destruct (Mem.perm_dec m1 b2 ofs2 Max Nonempty); try contradiction.
               ** eapply Inj23; try eassumption. eapply Mem.perm_extends; eassumption. eapply Mem.perm_extends; eassumption.
       * destruct (INC2 _ _ _ HeqJb2 H1) as [AA BB]. rewrite AA in *.
         remember (B2 b2) as q2; symmetry in Heqq2; destruct q2.
         ++ admit. (*readonly blocks mapped by j*)
         ++ assert (Mem.perm_order' ((Mem.mem_access m1') !! b2 ofs2 Max) Nonempty).
            { destruct (valid_block_dec m2 b2); trivial.
              destruct (Mem.perm_dec m1 b2 ofs2 Max Nonempty); trivial. contradiction. }
            clear H3.
            remember (B2 b1) as q1; symmetry in Heqq1; destruct q1.
            -- left; intros N; subst b2'.
               specialize (GSep _ _ _ HeqJb2 H1).
               apply (HB23 _ _ _ HeqJb1) in Heqq1.
               (*rewrite (RDOs_are_globals3 _ Heqq1) in GSep. congruence.*)
               specialize (RDOs_are_globals3 _ Heqq1); clear - RDOs_are_globals3 GSep; xomega.
            -- remember (L1 b1) as w1; symmetry in Heqw1; destruct w1.
               ** left; intros N; subst b2'.
                  rewrite (WDj _ _ _ HeqJb1) in Heqw1. congruence.
               ** destruct (Mem.perm_dec m1 b1 ofs1 Max Nonempty); try contradiction.
                  eapply Inj13'; eassumption.
     - remember (B2 b1) as q1; symmetry in Heqq1; destruct q1.
       {  admit. (*readonly blocks mapped by j*) }
       remember (j b2) as Jb2; symmetry in HeqJb2; destruct Jb2.
       * destruct p. assert (jj_b2 := INC1 _ _ _ HeqJb2). rewrite H1 in jj_b2; inv jj_b2.
         destruct (INC2 _ _ _ HeqJb1 H0) as [AA BB]. rewrite AA in *.
         destruct (valid_block_dec m2 b2).
         Focus 2. elim n. eapply Mem.valid_block_inject_1. apply HeqJb2. eassumption.
         remember (valid_block_dec m2 b1) as s; symmetry in Heqs; destruct s.
         { remember (B2 b2) as q2; symmetry in Heqq2; destruct q2.
           + left; intros N; subst b1'. clear H2.
             specialize (GSep _ _ _ HeqJb1 H0).
             apply (HB23 _ _ _ HeqJb2) in Heqq2.
             (*rewrite (RDOs_are_globals3 _ Heqq2) in GSep; congruence.*)
               specialize (RDOs_are_globals3 _ Heqq2); clear - RDOs_are_globals3 GSep; xomega.
           + destruct (Mem.perm_dec m1 b1 ofs1 Max Nonempty); try contradiction.
             remember (L1 b2) as w2; symmetry in Heqw2; destruct w2.
             - left; intros N; subst b1'.
               rewrite (WDj _ _ _ HeqJb2) in Heqw2. congruence.
             - destruct (Mem.perm_dec m1 b2 ofs2 Max Nonempty); try contradiction.
               eapply Inj13'; eassumption. }
         { clear Heqs.
           remember (B2 b2) as q2; symmetry in Heqq2; destruct q2.
           + left; intros N; subst b1'. 
             specialize (GSep _ _ _ HeqJb1 H0).
             apply (HB23 _ _ _ HeqJb2) in Heqq2.
             (*rewrite (RDOs_are_globals3 _ Heqq2) in GSep; congruence.*)
             specialize (RDOs_are_globals3 _ Heqq2); clear - RDOs_are_globals3 GSep; xomega.
           + remember (L1 b2) as w2; symmetry in Heqw2; destruct w2.
             - left; intros N; subst b1'.
               rewrite (WDj _ _ _ HeqJb2) in Heqw2; congruence.
             - destruct (Mem.perm_dec m1 b2 ofs2 Max Nonempty); try contradiction.
               eapply Inj13'; eassumption. }
       * destruct (INC2 _ _ _ HeqJb1 H0) as [AA1 BB1].
         destruct (INC2 _ _ _ HeqJb2 H1) as [AA2 BB2]. rewrite AA1, AA2 in *.
         assert (P1: Mem.perm_order' ((Mem.mem_access m1') !! b1 ofs1 Max) Nonempty).
         { destruct (valid_block_dec m2 b1); trivial.
           destruct (Mem.perm_dec m1 b1 ofs1 Max Nonempty); trivial. contradiction. }
         clear H2.
         remember (B2 b2) as q2; symmetry in Heqq2; destruct q2.
         {   admit. (*readonly blocks mapped by j*) }
         assert (P2: Mem.perm_order' ((Mem.mem_access m1') !! b2 ofs2 Max) Nonempty).
         { destruct (valid_block_dec m2 b2); trivial.
           destruct (Mem.perm_dec m1 b2 ofs2 Max Nonempty); trivial. contradiction. }
         eapply Inj13'; eassumption.
   + intros. unfold Mem.perm in H0. rewrite ACCESS in H0. unfold mem_add_acc in H0.
     remember (j b) as jb; symmetry in Heqjb; destruct jb.
     - destruct p. specialize (INC1 _ _ _ Heqjb). rewrite INC1 in H; inv H.
       destruct (valid_block_dec m2 b).
       { destruct (B2 b).
         + eapply Inj23; eassumption.
         + destruct (L1 b).
           - destruct (Mem.perm_dec m1 b (Int.unsigned ofs) Max Nonempty);
             destruct (Mem.perm_dec m1 b (Int.unsigned ofs - 1) Max Nonempty).
             * eapply Inj13'; eassumption.
             * eapply Inj23; try eassumption. left. eapply Mem.perm_extends; eassumption.
             * eapply Inj23; try eassumption. right. eapply Mem.perm_extends; eassumption.
             * eapply Inj23; eassumption.
           - destruct (Mem.perm_dec m1 b (Int.unsigned ofs) Max Nonempty);
             destruct (Mem.perm_dec m1 b (Int.unsigned ofs - 1) Max Nonempty).
             * eapply Inj13'; eassumption.
             * eapply Inj23; try eassumption. left. eapply Mem.perm_extends; eassumption.
             * eapply Inj23; try eassumption. right. eapply Mem.perm_extends; eassumption.
             * destruct H0; contradiction. }
       { eapply Inj13'; eassumption. }
    - destruct (INC2 _ _ _ Heqjb H) as [AA BB]. rewrite AA in *.
       destruct (valid_block_dec m2 b).
       { remember (B2 b) as q; symmetry in Heqq; destruct q.
         + admit. (*readonly blocks mapped by j*) 
         + destruct (Mem.perm_dec m1 b (Int.unsigned ofs) Max Nonempty);
             destruct (Mem.perm_dec m1 b (Int.unsigned ofs - 1) Max Nonempty).
             * eapply Inj13'; eassumption.
             * destruct H0; try contradiction. eapply Inj13'; try eassumption. left; assumption.
             * destruct H0; try contradiction. eapply Inj13'; try eassumption. right; assumption.
             * destruct H0; try contradiction. }
       { eapply Inj13'; eassumption. }
  + (*perm_inv*)
    intros b2 ofs b3; intros. destruct (Mem.mi_perm_inv _ _ _ Inj13' _ _ _ _ _ _ H H0).
    left. eapply Mem.perm_extends; eassumption.
    destruct (Mem.perm_dec m2' b2 ofs Max Nonempty). 2: right; trivial. left.
    unfold Mem.perm in p0. rewrite ACCESS in p0. unfold mem_add_acc in p0.
    unfold Mem.perm. rewrite ACCESS. unfold mem_add_acc. clear ACCESS CONT.
    remember (j b2) as s; symmetry in Heqs; destruct s.
    { destruct p1.
      specialize (INC1 _ _ _ Heqs). rewrite INC1 in H; inv H.
      destruct (valid_block_dec m2 b2).
      Focus 2. solve [elim n; eapply Mem.valid_block_inject_1; eassumption].
      remember (B2 b2) as q; symmetry in Heqq; destruct q.
      * apply (HB23 _ _ _ Heqs) in Heqq. 
        eapply RDOnly_fwd3 in H0; trivial.
        destruct (Mem.mi_perm_inv _ _ _ Inj23 _ _ _ _ _ _ Heqs H0); trivial. contradiction.
        instantiate (1:=33). (*dummy*) admit. (*RDO*) admit. (*RDO*)
      * remember (L1 b2) as w; symmetry in Heqw; destruct w.
        ++ destruct (Mem.perm_dec m1 b2 ofs Max Nonempty). contradiction.
           destruct UnchTgt as [_ UP _].
           apply UP in H0.
           -- destruct (Mem.mi_perm_inv _ _ _ Inj23 _ _ _ _ _ _ Heqs H0); trivial. contradiction.
           -- split. rewrite <- (WDj _ _ _ Heqs); trivial.
              intros. destruct (eq_block b1 b2).
              ** subst. rewrite J in Heqs; inv Heqs. assert (ofs + delta-delta= ofs) by omega. rewrite H2; trivial.
              ** intros N. eapply Mem.perm_extends in N. 2: eassumption.
                 destruct (Mem.mi_no_overlap _ _ _ Inj23 _ _ _ _ _ _ _ _ n0 J Heqs N p0).
                 congruence. omega.
           -- eapply Inj23; eassumption.
        ++ destruct (Mem.perm_dec m1 b2 ofs Max Nonempty); contradiction. }
    { destruct (INC2 _ _ _ Heqs H) as [AA BB].
      rewrite AA in *.
      destruct (valid_block_dec m2 b2); try contradiction.
      remember (B2 b2) as q; symmetry in Heqq; destruct q.
      +  admit. (*readonly blocks mapped by j*) 
      + destruct (Mem.perm_dec m1 b2 ofs Max Nonempty); try contradiction. } }
intuition.
red; intros. red; intros. admit. (*RDO*)

Admitted.
End Interpolation_EI.