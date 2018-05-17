Require Import Events.
Require Import Memory.
Require Import Coqlib.
Require Import Values.
Require Import Maps.
Require Import Integers.

Require Import VST.msl.Axioms.
Require Import VST.coarse_sepcomp.coarse_defs.
Require Import VST.coarse_sepcomp.coarse_base.
Require Import VST.coarse_sepcomp.interpolation_II_defs.
Require Import VST.coarse_sepcomp.interpolation_II_construction.

Section Interpolation_II.
Variable (m1 m2 m3 m1' m3': mem) 
      (j1 j2 j':meminj)
      (LS LM LT B1 B2 B3: Blockset)
      (INC : inject_incr (compose_meminj j1 j2) j')
      (FE : full_ext LS j1 j2)
      (WDmu12 (*j1_LS_LM*): forall b1 b2 d, j1 b1 = Some (b2, d) -> LS b1 = LM b2)
      (WDmu23 (*j2_LM_LT*): forall b2 b3 d, j2 b2 = Some (b3, d) -> LM b2 = LT b3)

      (SEP: esep m1 (compose_meminj j1 j2) j' m3 LT)
      (LSvalid : forall b, LS b = true -> Mem.valid_block m1 b)
      (LMvalid : forall b, LM b = true -> Mem.valid_block m2 b)
      (LTvalid : forall b, LT b = true -> Mem.valid_block m3 b)
      (J1_valid: forall b1 b2 d, j1 b1 = Some (b2, d) -> Mem.valid_block m1 b1 /\ Mem.valid_block m2 b2)
      (J2_valid: forall b2 b3 d, j2 b2 = Some (b3, d) -> Mem.valid_block m2 b2 /\ Mem.valid_block m3 b3)

      (MInj12 : Mem.inject j1 m1 m2) 
      (MInj23 : Mem.inject j2 m2 m3)
      (Jvalid': forall b1 b3 d, j' b1 = Some(b3,d) -> Mem.valid_block m1' b1 /\ Mem.valid_block m3' b3)
      (MInj13': Mem.inject j' m1' m3')

      (Fwd1 : mem_forward m1 m1')
      (Fwd3 : mem_forward m3 m3')
      (RDOnly_fwd1: RDOnly_fwd m1 m1' B1)
      (RDOnly_fwd3: RDOnly_fwd m3 m3' B3)
      (B3sep: forall b1 b3 d, (compose_meminj j1 j2) b1 = None -> j' b1 = Some(b3,d) -> B3 b3 = false)
      (B2_LM: forall b, B2 b = true -> LM b = false)
      (B2valid : forall b, B2 b = true -> Mem.valid_block m2 b /\ forall ofs, ~ Mem.perm m2 b ofs Max Writable)
      (B2_B3: forall b2 b3 d, j2 b2 = Some (b3, d) -> B2 b2 = true -> B3 b3 = true)
      (B2_B1: forall b1 b2 d, j1 b1 = Some(b2,d) -> B2 b2 = true -> B1 b1 = true)

      (UnchSrc : Mem.unchanged_on (fun b _ => LS b = true /\ compose_meminj j1 j2 b = None) m1 m1')
      (UnchTgt : Mem.unchanged_on (fun b z => LT b = true /\ loc_out_of_reach (compose_meminj j1 j2) m1 b z) m3 m3').

Lemma interp_II_mem_only:
exists (j1' j2' : meminj) (m2' : mem),
  inject_incr j1 j1' /\ esep m1 j1 j1' m2 LM /\(forall b1 b2 d, j1' b1 = Some(b2,d) -> Mem.valid_block m1' b1 /\ Mem.valid_block m2' b2) /\
  inject_incr j2 j2' /\ esep m2 j2 j2' m3 LT /\ (forall b1 b2 d, j2' b1 = Some(b2,d) -> Mem.valid_block m2' b1 /\ Mem.valid_block m3' b2) /\
  full_ext LS j1' j2' /\ j' = compose_meminj j1' j2' /\
  Mem.inject j1' m1' m2' /\ Mem.inject j2' m2' m3' /\
  mem_forward m2 m2' /\ RDOnly_fwd m2 m2' B2 /\
  Mem.unchanged_on
    (fun (b : block) (z : Z) => LM b = true /\ loc_out_of_reach j1 m1 b z) m2 m2' /\
  Mem.unchanged_on (fun (b : block) (_ : Z) => LM b = true /\ j2 b = None) m2 m2' /\
  (forall b2 b3 d (J2': j2' b2 = Some (b3, d)),
     j2 b2 = Some (b3, d) \/
     j2 b2 = None /\ j1' (b2 - (Mem.nextblock m2))%positive = Some (b2, 0) /\
                     j' (b2 - (Mem.nextblock m2))%positive = Some (b3, d) /\ 
                     (compose_meminj j1 j2) ((b2 - (Mem.nextblock m2))%positive) = None /\ 
                     (~ Mem.valid_block m2 b2)).
Proof. intros. rename j1 into j12. rename j2 into j23.
  set (extern_of j12 LS) as e12 in *;
  set (extern_of j23 LM) as e23 in *;
  set (extern_of j' LS) as e' in *.
  set (local_of j12 LS) as l12 in *;
  set (local_of j23 LM) as l23 in *;
  set (local_of j' LS) as l' in *;
  set (Mem.nextblock m2) as sizeM2 in *.
  remember (mkInjections (Mem.nextblock m2) e12 e23 e') as output; symmetry in Heqoutput.
  destruct output as [e12' e23'].
  set (j12' := join l12 e12') in *.
  set (j23' := join l23 e23') in *.
  
  assert (extern_of_e12': is_extern e12' LS).
  { red; unfold extern_of. extensionality b. remember (e12' b) as d.
    destruct d. 2: destruct (LS b); trivial. destruct p; symmetry in Heqd.
    destruct (MKI_Some12 _ _ _ _ _ _ Heqoutput _ _ _ Heqd) as [E12 | [E12 [b3 [d [E' [BB D]]]]]].
    + destruct (extern_of_ESome _ _ _ _ E12) as [HL _]; rewrite HL; trivial.
    + subst z e'. destruct (extern_of_ESome _ _ _ _ E') as [HL _]; rewrite HL; trivial.
  }
  assert (ext12': forall b1 b2 d, e12' b1 = Some (b2,d) -> LS b1 = false /\ LM b2 = false).
  { intros. exploit MKI_Some12. eassumption. eassumption.
    intros [E12 | [E12 [b [dd [E' [BB2 D]]]]]].
    + subst e12. destruct (extern_of_ESome _ _ _ _ E12); clear E12. split; trivial. rewrite <- (WDmu12 _ _ _ H1); trivial.
    + subst d e'. destruct (extern_of_ESome _ _ _ _ E'); clear E'. split; trivial.
      remember (LM b2) as q; destruct q; trivial. symmetry in Heqq.
      eapply LMvalid in Heqq. subst b2. unfold Mem.valid_block in Heqq. xomega. }

  assert (local_of_e12': local_of e12' LS = (fun b => None)).
  { unfold local_of. extensionality b. remember (LS b) as q.
    destruct q; trivial. 
    remember (e12' b) as d. destruct d; trivial. symmetry in Heqd; destruct p. 
    destruct (MKI_Some12 _ _ _ _ _ _ Heqoutput _ _ _ Heqd) as [E12 | [E12 [b3 [d [E' [BB D]]]]]].
    + destruct (extern_of_ESome _ _ _ _ E12) as [HL _]; congruence. 
    + subst z e'. destruct (extern_of_ESome _ _ _ _ E') as [HL _]; congruence. 
  }
  assert (E_INC12: extern_incr j12 j12' LS).
  { split. 
    + subst j12' l12. rewrite extern_of_join_local_x, extern_of_e12'.
      eapply MKI_incr12. apply  Heqoutput.
    + subst j12' l12. rewrite local_of_join_local_x, local_of_e12', join_None_rightneutral; trivial. }

  assert (extern_of_e23': is_extern e23' LM).
  { red; unfold extern_of. extensionality b. remember (LM b) as q.
    destruct q; trivial. symmetry in Heqq.
    remember (e23' b) as d. destruct d; trivial. destruct p; symmetry in Heqd.
    destruct (MKI_Some23 _ _ _ _ _ _ Heqoutput _ _ _ Heqd) as [E23 | [E23 [E' [E12 X]]]].
    + destruct (extern_of_ESome _ _ _ _ E23) as [HL _]; congruence. 
    + assert (VB: Mem.valid_block m2 b) by (apply LMvalid; trivial).
      clear - VB X. unfold Mem.valid_block in VB. rewrite Pcompare_eq_Gt in X. xomega. }


  assert (ext23': forall b2 b3 d, e23' b2 = Some (b3,d) -> LM b2 = false /\ LT b3 = false).
  { intros. exploit MKI_Some23. eassumption. eassumption.
    intros [E23 | [E23 [E' [E12 BB2]]]].
    + subst e23. destruct (extern_of_ESome _ _ _ _ E23); clear E23. split; trivial. rewrite <- (WDmu23 _ _ _ H1); trivial.
    + subst e'. rewrite Pcompare_eq_Gt in BB2.
      destruct (extern_of_ESome _ _ _ _ E'); clear E'.
      split.
      - remember (LM b2) as q; destruct q; trivial. symmetry in Heqq. 
        eapply LMvalid in Heqq. clear - BB2 Heqq. unfold Mem.valid_block in Heqq. xomega.
      - remember (LT b3) as q; destruct q; trivial. symmetry in Heqq. exfalso.
        destruct (SEP ((b2 - Mem.nextblock m2)%positive) b3 d); trivial.
        * unfold compose_meminj.
          remember (j12 (b2 - Mem.nextblock m2)%positive) as w.
          destruct w; trivial; symmetry in Heqw.
          destruct p. destruct (J1_valid _ _ _ Heqw).
          remember (j23 b) as r; symmetry in Heqr. destruct r; trivial.
          destruct p. specialize (INC ((b2 - Mem.nextblock m2)%positive) b0).
          unfold compose_meminj in INC. rewrite  Heqw, Heqr in INC.
          erewrite INC in H1; [inv H1 | reflexivity].
          rewrite <- (WDmu23 _ _ _ Heqr) in Heqq.
          rewrite (WDmu12 _ _ _ Heqw) in H0; congruence.
        * rewrite H3 in Heqq. congruence. auto. }

  assert (local_of_e23': local_of e23' LM = (fun b => None)).
  { unfold local_of. extensionality b. remember (LM b) as q.
    destruct q; trivial. symmetry in Heqq.
    remember (e23' b) as d. destruct d; trivial. symmetry in Heqd; destruct p. 
    destruct (MKI_Some23 _ _ _ _ _ _ Heqoutput _ _ _ Heqd) as [E23 | [E23 [E' [E12 X]]]].
    + destruct (extern_of_ESome _ _ _ _ E23) as [HL _]; congruence. 
    + assert (VB: Mem.valid_block m2 b).
      { unfold is_extern, extern_of in extern_of_e23'. rewrite <- extern_of_e23' in *. simpl in *.
        rewrite Heqq in Heqd; congruence. } 
      clear - VB X. unfold Mem.valid_block in VB. rewrite Pcompare_eq_Gt in X. xomega. } 

  assert (E_INC23: extern_incr j23 j23' LM).
  { split. 
    + subst j23' l23. rewrite extern_of_join_local_x, extern_of_e23'.
      eapply MKI_incr23. apply  Heqoutput.
    + subst j23' l23. rewrite local_of_join_local_x, local_of_e23', join_None_rightneutral; trivial. }

  assert (full' : full_comp e12' e23').
  { eapply MKI_norm; eauto.
    + intros b1 b2 d1 E12. unfold full_ext in FE. subst e12 e23. destruct (extern_of_ESome _ _ _ _ E12) as [HL1 J12].
      destruct (FE _ _ _ J12 HL1) as [b3 [d2 J23]].
      exists b3, d2. rewrite extern_of_Ifalse; trivial. rewrite <- (WDmu12 _ _ _ J12); trivial.
    + intros b2 [b3 d2] E23. subst e23. 
      destruct (extern_of_ESome _ _ _ _ E23) as [HL2 J23].
      eapply (Mem.valid_block_inject_1 j23); eassumption. }

   assert (local_jj': local_of j' LS = local_of (compose_meminj j12 j23)  LS).
   { (*destruct ExtIncr as [EIa EIb].*) extensionality b.
         unfold local_of. remember (LS b) as d. destruct d; trivial.
         remember (compose_meminj j12 j23 b) as q.
         destruct q; symmetry in Heqq.
         + destruct p. apply INC; trivial.
         + remember (j' b) as w.
           destruct w; trivial; symmetry in Heqw, Heqd.
           destruct p. destruct (SEP _ _ _ Heqq Heqw). specialize (LSvalid _ Heqd); congruence. }

  assert (INC12:= extern_incr_inject_incr _ _ _ E_INC12).
  assert (INC23:= extern_incr_inject_incr _ _ _ E_INC23).
  assert (HE': e' = compose_meminj e12' e23').
  { eapply MKIcomposition; eauto.
     + red; intros b1 b2 d1 E12. subst e12 e23. 
       destruct (extern_of_ESome _ _ _ _ E12) as [X1 X2]; clear E12.
       destruct (FE _ _ _ X2 X1) as [b3 [d2 E23]]. rewrite (WDmu12 _ _ _ X2) in X1.
       rewrite extern_of_Ifalse; trivial. exists b3, d2; trivial.
     + subst e12 e23 e'. intros b1 b3 d E123.
       rewrite compose_meminj_extern in E123; trivial.
       destruct (extern_of_ESome _ _ _ _ E123) as [X1 X2]; clear E123.
       apply INC in X2. rewrite extern_of_Ifalse; trivial.
     + intros b2 (b3, d2) E23. destruct (extern_of_ESome _ _ _ _ E23) as [X1 X2]; clear E23.
       eapply Mem.valid_block_inject_1; eassumption.
  }
  assert (J': j' = compose_meminj j12' j23').
  { clear Heqoutput. rewrite (join_local_extern j' LS); subst e' j12' j23'.
       subst l12 l23. rewrite HE', local_jj'.
       erewrite <- compose_meminj_local. 2: apply WDmu12. 
       apply compose_meminj_join.
       - rewrite <- extern_of_e12'. eapply disjoint_local_extern.
       - intros. rewrite <- extern_of_e23'. apply extern_of_Itrue.
         destruct (local_of_ESome _ _ _ _ H) as [HL J12].
         rewrite <- (WDmu12 _ _ _ J12); trivial.
       - intros. destruct (full' _ _ _ H) as [b3 [d2 E23']]. apply local_of_Ifalse.
         rewrite <- extern_of_e23' in E23'.
         apply (extern_of_ESome _ _ _ _ E23'). }
  
  assert (FE': full_ext LS j12' j23').
  { red; intros. red in FE.
    remember (j12 b1) as d.
    destruct d; symmetry in Heqd.
    + destruct p. destruct (FE _ _ _ Heqd H0) as [b3 [d2 J23]]. 
      rewrite (INC12 _ _ _ Heqd) in H; inv H. do 2 eexists; apply INC23; eassumption.
    + specialize (full' b1 b2 delta1); subst j12'. apply joinD_Some in H. destruct H as [L12 | [L12 E12']].
      - subst l12. unfold local_of in L12. rewrite H0 in L12; discriminate.
      - subst j23'. destruct (full' E12') as [bb [dd E23']]. exists bb, dd. apply joinI. right; split; trivial.
        subst l23. unfold local_of. destruct (ext12' _ _ _ E12') as [_ X]; rewrite X; trivial. }

  assert (VBj12: meminj_validblock_2 j12 m2).
  { red; intros. eapply Mem.valid_block_inject_2; eassumption. }

  assert (VBj12': forall b1 b2 d1 (J12': j12' b1 = Some(b2,d1)),
           Mem.valid_block m1' b1 /\ Plt b2 (mem_add_nb m1' m2)).
  { intros. unfold mem_add_nb.
    subst j12'. destruct (joinD_Some _ _ _ _ _ J12') as [LOC | [LOC EXT]]; clear J12'.
    + subst l12. destruct (local_of_ESome _ _ _ _ LOC); clear LOC.
      split. apply Fwd1. eauto.
      assert (Plt b2 (Mem.nextblock m2)). apply (J1_valid _ _ _ H0). xomega. 
    + exploit MKI_Some12. eassumption. eassumption.
      intros [E12 | [E12 [b3 [d [E' [B' D]]]]]].
      - subst e12. destruct (extern_of_ESome _ _ _ _ E12); clear E12.
        split. apply Fwd1.  apply (J1_valid _ _ _ H0).
        assert (Plt b2 (Mem.nextblock m2)). apply (J1_valid _ _ _ H0).
        xomega.
      - subst b2 d1 e'. destruct (extern_of_ESome _ _ _ _ E'); clear E'.
        assert (Plt b1 (Mem.nextblock m1')) by (eapply Jvalid'; eauto).
        split. apply H1. xomega. }
  assert (VBj23': forall b2 b3 d2 (J23': j23' b2 = Some(b3,d2)),
            Plt b2 (mem_add_nb m1' m2) /\ Mem.valid_block m3' b3).
  { intros. unfold mem_add_nb.
    subst j23'. destruct (joinD_Some _ _ _ _ _ J23') as [LOC | [LOC EXT]]; clear J23'.
    + subst l23. destruct (local_of_ESome _ _ _ _ LOC); clear LOC.
      destruct (J2_valid _ _ _ H0).
      split. red in H1; xomega.
      apply Fwd3; trivial.
    + exploit MKI_Some23. eassumption. eassumption.
      intros [E23 | [E23 [E' [E12 GT]]]].
      - subst e23. destruct (extern_of_ESome _ _ _ _ E23); clear E23.
        destruct (J2_valid _ _ _ H0).
        split. red in H1; xomega.
        apply Fwd3; eauto.
      - subst e'. destruct (extern_of_ESome _ _ _ _ E'); clear E'.
        destruct (Jvalid' _ _ _ H0). split; trivial. clear - GT H1. 
        unfold Mem.valid_block, Plt in H1. apply Pos.compare_gt_iff in GT; xomega. }
 
  assert (Esep1': esep m1 j12 j12' m2 LM).
  { intros b1 b2 d J1 J1'. subst j12'. apply joinD_Some in J1'. destruct J1' as [L1 | [L1 E1]]; subst l12. 
    + rewrite (inject_incr_local_of _ _ _ _ _ L1) in J1; discriminate.
    + destruct (ext12' _ _ _ E1). split; intros; trivial.
      destruct (full' b1 _ _ E1) as [b3 [d2 E2]].
      apply (SEP b1 b3 (d+d2)); subst; unfold compose_meminj. rewrite J1; trivial.
      assert (JN1: join (local_of j12 LS) e12' b1 = Some(b2, d)). apply joinI; right; split; trivial.
      subst j23'.
      assert (JN2: join l23 e23' b2 = Some(b3, d2)). apply joinI; right; split; trivial. subst l23. unfold local_of. rewrite H0; trivial.
      rewrite JN1, JN2; trivial. }  
  assert (Esep2': esep m2 j23 j23' m3 LT).
  { intros b2 b3 d J2 J2'. subst j23'. apply joinD_Some in J2'. destruct J2' as [L2 | [L2 E2]]; subst l23. 
    + unfold local_of in L2; rewrite J2 in L2. destruct (LM b2); discriminate.
    + destruct (ext23' _ _ _ E2). split; intros; trivial.
      destruct (MKI_Some23 _ _ _ _ _ _ Heqoutput _ _ _ E2) as [E | [E [E' [A B]]]].
      - subst e23. unfold extern_of in E. rewrite J2, H in E; congruence.
      - apply Pos.compare_nle_iff in B. unfold Mem.valid_block. xomega. }  
  (*
  assert (Gsep12: globals_separate ge2 j12 j12').
  { intros b1 b2 d1 J12 J12'.
    remember (isGlobalBlock ge2 b2) as g; destruct g; trivial; symmetry in Heqg.
    specialize (GV2 _ Heqg).
    destruct (FE' _ _ _ J12') as [b3 [d2 J23']]; clear FE'.
    + remember (LS b1) as q; destruct q; trivial; symmetry in Heqq. 
      apply LSvalid in Heqq.
      destruct (Esep1' _ _ _ J12 J12'); contradiction.
    + exploit (Gsep b1 b3 (d1+d2)); subst j'; unfold compose_meminj.
      - rewrite J12; trivial.
      - rewrite J12', J23'; trivial.
      - rewrite <- (G23 b2 b3 d2), Heqg; trivial. 
        remember (j23 b2) as w; destruct w; symmetry in Heqw.
        * destruct p; rewrite (INC23 _ _ _ Heqw) in J23'; rewrite J23'; trivial.
        * destruct (Esep2' _ _ _ Heqw J23'); contradiction. }

  assert (Gsep23: globals_separate ge3 j23 j23').
  { intros b2 b3 d2 J23 J23'.
    remember (isGlobalBlock ge3 b3) as g; destruct g; trivial; symmetry in Heqg.
    destruct E_INC23 as [LOC23 EXT23].
    destruct (Esep2' _ _ _ J23 J23'); clear Esep2'.
    subst j23'; apply joinD_Some in J23'; subst l23. destruct J23' as [L23 | [L23 E23']].
    + unfold local_of in L23; rewrite J23 in L23. destruct (LM b2); discriminate.
    + remember (isGlobalBlock ge2 b2) as g2; destruct g2; symmetry in Heqg2. 
      apply GV2 in Heqg2; contradiction.
      destruct (MKI_Some23 _ _ _ _ _ _ Heqoutput _ _ _ E23') as [E23 | [E23 [E' [E12 _]]]].
      - subst e23. unfold extern_of in E23; rewrite J23 in E23. destruct (LM b2); discriminate.
      - clear HE'; subst e'. unfold extern_of in E'. remember (LS (b2 - Mem.nextblock m2)%positive) as w; destruct w; [discriminate | symmetry in Heqw].
        rewrite (Gsep ((b2 - Mem.nextblock m2)%positive) b3 d2) in Heqg; [ rewrite Heqg; trivial | | trivial]; clear Gsep.
        remember (compose_meminj j12 j23 ((b2 - Mem.nextblock m2)%positive)) as q; destruct q; [symmetry in Heqq; destruct p | trivial].
        apply compose_meminjD_Some in Heqq. destruct Heqq as [bb [d1 [d3 [J12 [JJ23 D]]]]].
        rewrite (join_local_extern j12 LS) in J12. apply joinD_Some in J12.
        subst l12 e12. rewrite E12 in J12. unfold local_of in J12; rewrite Heqw in J12.
        destruct J12 as [X | [_ X]]; inv X. }*)

  exploit (interpolation_II_exists j12 j23 j12' m1 m1' m2 LM B2(*(ReadOnlyBlocks ge2)*)); trivial.
  { red; intros. eapply VBj12'; eassumption. }
  intros [m2' [H_CONT [H_ACCESS NB2']]].

(*  rewrite J' in RVinj; destruct (val_inject_split _ _ j12' j23' RVinj) as [ret2 [RVinj12 RVinj23]].*)

  rewrite <- NB2' in *. exists j12', j23', m2'. (*, ret2
  assert (HasType2: Val.has_type ret2 tp).
  { subst. clear - RVinj12 RVinj23 HasType1 HasType3.
    inv RVinj23; simpl; trivial. }*)
  split; trivial. split; trivial. split; trivial. split; trivial. split; trivial. split. apply VBj23'. 
  (*split; trivial. split; trivial.*) split; trivial.
  split; trivial.
  assert (Fwd2: mem_forward m2 m2').
  { intros b2 Vb2; split.
    + unfold Mem.valid_block in *.
                  rewrite NB2'.
                  unfold mem_add_nb.
                  xomega.
    +  intros ofs per; unfold Mem.perm. rewrite H_ACCESS; unfold ACCESS.
             destruct (valid_block_dec m2 b2); try contradiction.
             destruct (B2 b2); trivial. 
             (*destruct (ReadOnlyBlocks ge2 b2); trivial. *)
             remember (source j12 m1 b2 ofs) as q.
             destruct q; trivial.
             - destruct (source_SomeE _ _ _ _ _ Heqq) as [b1 [delta' [ofs1 [invertible [leq [mapj [mperm ofs_add]]]]]]].
               subst ofs; intros H0. eapply MInj12. eassumption.
               inversion invertible; clear invertible. subst. 
               destruct (Fwd1 _ leq) as [VB' Perms1 (*FwdMax1]*)].
               eapply Perms1. destruct (LM b2); assumption.
             - remember (LM b2) as l; destruct l. trivial. 
               destruct (j23 b2); intros HH;try destruct p; trivial; inversion HH. }
  assert (RDOnly2: RDOnly_fwd m2 m2' B2). (*same proof as in interp_IE, but for different H_ACCESS, H_CONT*)
  { clear - B2valid H_ACCESS H_CONT. red; intros b Hb. destruct (B2valid _ Hb) as [VB2 RDOb2]. red; intros. 
    assert (P: forall i, 0 <= i < n -> forall k p, Mem.perm m2 b (ofs + i) k p <-> Mem.perm m2' b (ofs + i) k p).
    { intros. unfold Mem.perm; rewrite H_ACCESS. unfold ACCESS; simpl.
      destruct (valid_block_dec m2 b); [ rewrite Hb; split; trivial | contradiction]. }
    split; trivial. 
    remember (Mem.loadbytes m2' b ofs n) as q; remember (Mem.loadbytes m2 b ofs n) as p.
    symmetry in Heqq; symmetry in Heqp; destruct p; destruct q; trivial;
      try apply loadbytes_D in Heqp; try apply loadbytes_D in Heqq.
    - destruct Heqq; destruct Heqp; subst; f_equal; apply Mem.getN_exten; intros.
      rewrite (H_CONT b); clear H_CONT. unfold CONT; simpl.
      destruct (valid_block_dec m2 b); [ rewrite Hb; trivial | contradiction].
    - destruct Heqp; subst.
      destruct (Mem.range_perm_dec m2' b ofs (ofs + n) Cur Readable). 
      * apply Mem.range_perm_loadbytes in r. destruct r as [bytes R]; congruence.
      * elim n0; clear n0. red; intros. specialize (P (ofs0 - ofs)).
        rewrite Zplus_minus in P; apply P; [ omega | apply (H _ H0)].
    - destruct Heqq; subst.
      destruct (Mem.range_perm_dec m2 b ofs (ofs + n) Cur Readable). 
      * apply Mem.range_perm_loadbytes in r. destruct r as [bytes R]; congruence.
      * elim n0; clear n0. red; intros. specialize (P (ofs0 - ofs)).
        rewrite Zplus_minus in P; apply P; [ omega | apply (H _ H0)]. }
  assert (UnchSrc12 :Mem.unchanged_on (fun b z => LM b = true /\ loc_out_of_reach j12 m1 b z) m2 m2').
       { constructor.
         +  apply mem_forward_nextblock; apply Fwd2.
         + intros b2 ofs k p [Lb2 P] bval. unfold Mem.perm at 2.
           rewrite H_ACCESS; unfold ACCESS.
           rewrite Lb2.
           destruct (valid_block_dec m2 b2); try solve[contradict bval;trivial].
           destruct (B2 b2); simpl.
           - split; trivial.
           - remember (source j12 m1 b2 ofs) as q.
             destruct q; try solve [split; trivial].
             destruct (source_SomeE _ _ _ _ _ Heqq) as [bb [dd [zz [AA [BB [CC [DD EE]]]]]]].
             subst. elim (P _ _ CC). rewrite Z.add_simpl_r; trivial.
         + intros b2 ofs [Lb2 P] mperm. 
           rewrite H_CONT; unfold CONT. 
           rewrite Lb2. specialize (Mem.perm_valid_block _ _ _ _ _ mperm); intros VB2.
           destruct (valid_block_dec m2 b2); try contradiction.
           destruct (B2 b2); simpl; trivial.
             remember (source j12 m1 b2 ofs) as q.
             destruct q; try solve [split; trivial].
             destruct (source_SomeE _ _ _ _ _ Heqq) as [bb [dd [zz [AA [BB [CC [DD EE]]]]]]].
               subst. elim (P _ _ CC). rewrite Z.add_simpl_r; trivial. }
  assert (UnchMid: Mem.unchanged_on (fun b2 z => LM b2 = true /\ j23 b2 = None) m2 m2').
  { constructor.
         + apply mem_forward_nextblock; apply Fwd2.
         + intros b2 ofs k p [Lb2 J23] bval; unfold Mem.perm.
           rewrite H_ACCESS; unfold ACCESS.
           rewrite Lb2.
           destruct (valid_block_dec m2 b2); try solve[contradict bval;trivial]. 
           destruct (B2 b2); simpl. split; trivial.
           remember (source j12 m1 b2 ofs) as q.
           destruct q; try solve [split; trivial].
           destruct (source_SomeE _ _ _ _ _ Heqq) as [b1 [dd [zz [AA [BB [CC [DD EE]]]]]]].
           subst. destruct UnchSrc as [UnchA UnchB UnchC].
           destruct (UnchB b1 zz k p); trivial.
             - split. rewrite (WDmu12 _ _ _ CC); trivial. 
               unfold compose_meminj; rewrite CC, J23; trivial.
             - split; intros.
               * apply H; clear H H0.
                 exploit Mem.perm_inject_inv. apply MInj12. apply CC. apply H1.
                 intros [X | X]; trivial; contradiction.
               * eapply MInj12. eassumption. apply H0. apply H1.
         + intros b2 ofs [Lb2 J23] mperm.
           rewrite H_CONT; unfold CONT. 
           rewrite Lb2. specialize (Mem.perm_valid_block _ _ _ _ _ mperm); intros VB2.
           destruct (valid_block_dec m2 b2); try contradiction.
           destruct (B2 b2); simpl; trivial.
             remember (source j12 m1 b2 ofs) as q.
             destruct q; try solve [split; trivial].
             destruct (source_SomeE _ _ _ _ _ Heqq) as [b1 [dd [zz [AA [BB [CC [DD EE]]]]]]].
             subst.
             rewrite J23; trivial. }
  assert (Perm23':forall b2 b3 delta ofs k p, j23' b2 = Some (b3, delta) ->
               Mem.perm m2' b2 ofs k p -> Mem.perm m3' b3 (ofs + delta) k p).
  { intros b2 b3 delta ofs k p J23'.
             unfold Mem.perm. rewrite H_ACCESS; unfold ACCESS.
    destruct (joinD_Some _ _ _ _ _ J23') as [L23 | [L23 E23']]; clear J23'.
    + subst l23. destruct (local_of_ESome _ _ _ _ L23) as [L2true J23].
      rewrite L2true.
      destruct (valid_block_dec m2 b2).
      2: solve [elim n; eapply J2_valid; eauto].
      remember (B2 b2) as rdo; symmetry in Heqrdo; destruct rdo; simpl.
      * (*rewrite (GL2 _ (ReadOnlyBlocks_global _ _ Heqrdo)) in L2true; inv L2true. xx*) apply B2_LM in Heqrdo; congruence.
      * destruct (source j12 m1 b2 ofs) eqn:sour.
        - symmetry in sour.
          destruct (source_SomeE _ _ _ _ _ sour) 
                    as [b1 [d1 [ofs1 [pairs [bval [J12 [mperm ofss]]]]]]].
          subst. rewrite <- Zplus_assoc.
          eapply MInj13'.
          unfold compose_meminj. rewrite (INC12 _ _ _ J12). rewrite (INC23 _ _ _ J23); trivial.
        - symmetry in sour; intros. eapply UnchTgt.
          ++ rewrite <- (WDmu23 _ _ _ J23). split; trivial. red; intros b1 ? J0.
             destruct (compose_meminjD_Some _ _ _ _ _ J0) as [bb [dd1 [dd2 [K1 [K2 K3]]]]]; clear J0.
             subst delta0. intros N.
             destruct (eq_block bb b2).
             -- subst b2; rewrite J23 in K2; inv K2.
                eapply (source_NoneE _ _ _ _ sour b1).
                  eapply Mem.valid_block_inject_1. apply K1. apply MInj12.
                  eassumption.
                 assert (Arith: ofs + dd2 - (dd1 + dd2) = ofs - dd1) by omega.
                  rewrite Arith in N; trivial.
            -- exploit (Mem.mi_no_overlap _ _ _ MInj23 bb b3). apply n. eassumption. eassumption.
               eapply MInj12. eassumption. eassumption.
               eapply Mem.perm_max. eapply Mem.perm_implies. eassumption. constructor.
               intros [X | X]. congruence. omega.
          ++ eapply MInj23; eauto.
          ++ eapply MInj23; eauto. 
    + rewrite <- extern_of_e23' in E23'. 
      destruct (extern_of_ESome _ _ _ _ E23') as [L2false E23]; clear E23'; rename E23 into E23'.
      rewrite L2false.
      exploit MKI_Some23. eassumption. eassumption. 
      intros [E23 | [E23 [E' [E12 Bb2]]]].
      - subst e23. destruct (extern_of_ESome _ _ _ _ E23) as [_ J23].
        destruct (valid_block_dec m2 b2).
        2: elim n; eapply (Mem.valid_block_inject_1 j23); eassumption.
        remember (B2 b2) as q.
        destruct q; intros; symmetry in Heqq.
        * destruct (B2valid _ Heqq) as [_ RDOb2]. 
          exploit Mem.perm_inject. apply J23. eassumption. apply H. intros P3. 
          apply (B2_B3 _ _ _ J23) in Heqq.
          destruct (RDOnly_fwd3 _ Heqq 1 (ofs+delta)).
          ++ intros i I N. replace (ofs + delta + i) with (ofs+delta) in N by omega.
             eapply MInj23 in N. 2: eassumption. destruct N as [N | N].
             -- apply Mem.perm_max in N. apply (RDOb2 _ N). 
             -- apply N; clear - H. eapply Mem.perm_max. eapply Mem.perm_implies. eassumption. constructor.
          ++ specialize (H1 0); rewrite Zplus_0_r in H1. apply H1; [omega | trivial]. 
        * remember (source j12 m1 b2 ofs) as r .
          destruct r.
          ++ destruct (source_SomeE _ _ _ _ _ Heqr) 
                    as [b1 [d1 [ofs1 [pairs [bval [J12 [mperm ofss]]]]]]].
             subst p0 ofs j'. rewrite <- Zplus_assoc.
             eapply MInj13'. 
             unfold compose_meminj. rewrite (INC12 _ _ _ J12).
             rewrite (INC23 _ _ _ J23); trivial. apply H.
          ++ rewrite J23 in H. simpl in H; contradiction. 
      - destruct (valid_block_dec m2 b2).
        * exfalso. clear - v Bb2. rewrite Pcompare_eq_Gt in Bb2. unfold Mem.valid_block in v. xomega.
        * intros.
          remember (source j12' m1' b2 ofs) as r .
          destruct r.
          ++ destruct (source_SomeE _ _ _ _ _ Heqr) 
                    as [b1 [d1 [ofs1 [pairs [bval [J12 [mperm ofss]]]]]]].
             subst ofs p0. rewrite <- Zplus_assoc.
             eapply MInj13'. 2: eassumption.
             subst j'. unfold compose_meminj. rewrite J12.
               subst j23'. erewrite join_incr_right. reflexivity. subst l23. rewrite <- extern_of_e23'. apply disjoint_local_extern.
               assumption.
          ++ simpl in H; contradiction. } 

    assert (MInj12': Mem.inject j12' m1' m2').
       { (* Prove no overlapping of j12' first *)
         assert (no_overlap12': Mem.meminj_no_overlap j12' m1').
         { red; intros. destruct (eq_block b1' b2'). 2: left; assumption. subst b2'.
           destruct (joinD_Some _ _ _ _ _ H0) as [L12_1 | [L12_1 E12_1]]; clear H0.
           + destruct (local_of_ESome _ _ _ _ L12_1); clear L12_1. 
             destruct (joinD_Some _ _ _ _ _ H1) as [L12_2 | [L12_2 E12_2]]; clear H1.
               - destruct (local_of_ESome _ _ _ _ L12_2); clear L12_2.
                 eapply MInj12; try eassumption.
                 eapply Fwd1; trivial. eapply J1_valid; eassumption.
                 eapply Fwd1; trivial. eapply J1_valid; eassumption.
               - rewrite (WDmu12 _ _ _ H4) in H0. 
                 destruct (ext12' _ _ _ E12_2). congruence.
          + eapply MKI_no_overlap12.
           - apply Heqoutput. 
           - eapply meminj_no_overlap_rcni. eapply MInj12.
             subst e12. apply inject_incr_extern_of. 
           - eapply meminj_no_overlap_rcni. eapply MInj13'.
             subst e'. apply inject_incr_extern_of. 
           - trivial.
           - intros. eapply Mem.valid_block_inject_1. 
             eapply inject_incr_extern_of; eassumption. eassumption.
           - intros. eapply Mem.valid_block_inject_2. 
             eapply inject_incr_extern_of; eassumption. eassumption.
           - apply H.
           - eassumption.
           - destruct (ext12' _ _ _ E12_1). 
             subst j12'. destruct (joinD_Some _ _ _ _ _ H1) as [LL2 | [LL2 EE2]]; clear H1; trivial.
             subst l12. destruct (local_of_ESome _ _ _ _ LL2); clear LL2.
             rewrite (WDmu12 _ _ _ H5) in *; congruence.
           - trivial.
           - trivial. }
         
         (* Prove Mem.inject12'*)
         constructor; trivial.
         + (*Mem.mem_inj j12' m1' m2'*) constructor.
           - { intros b1 b2 delta ofs k p H H0.
               unfold Mem.perm; rewrite H_ACCESS; 
               unfold ACCESS.

               subst j12'; apply joinD_Some in H; 
               destruct H as [L12 | [L12 E12']].
               + subst l12. destruct (local_of_ESome _ _ _ _ L12) as [HL1 J12]; clear L12.
                 destruct (valid_block_dec m2 b2). 2: elim n; eapply J1_valid; eassumption.
                 rewrite <- (WDmu12 _ _ _ J12), HL1.
                 remember (B2 b2) as r2; destruct r2; simpl.
                 - clear - Heqr2 B2valid B2_LM WDmu12 HL1 J12. symmetry in Heqr2. destruct (B2valid _ Heqr2) as [_ RDOb2]. 
                   apply B2_LM in Heqr2. rewrite (WDmu12 _ _ _ J12) in HL1. congruence.
                 - erewrite source_SomeI; try eassumption.
                   * apply MInj12.
                   * apply Fwd1. eapply J1_valid; eassumption.
                     eapply Mem.perm_implies. eapply Mem.perm_max; eassumption. constructor.
               + exploit MKI_Some12. eassumption. apply E12'. intros [E12 | [E12 [b3 [d [E' [Hb2 D]]]]]].
                 - subst e12. destruct (extern_of_ESome _ _ _ _ E12) as [HL1 J12]; clear E12.
                   rewrite <- (WDmu12 _ _ _ J12), HL1.
                   destruct (valid_block_dec m2 b2). 2: elim n; eapply J1_valid; eassumption.
                   remember (B2 b2) as r2; destruct r2; simpl; symmetry in Heqr2.
                   * destruct (B2valid _ Heqr2) as [_ RDOb2].
                     specialize (B2_B1 _ _ _ J12 Heqr2).
                     destruct (RDOnly_fwd1 _ B2_B1 1 ofs).
                     ++ intros i I N. replace (ofs + i) with ofs in N by omega. apply Mem.perm_max in N.
                        apply (RDOb2 (ofs+delta)). eapply MInj12; eassumption.
                     ++ specialize (H1 0); rewrite Zplus_0_r in H1. apply H1 in H0; [|omega].
                        eapply MInj12; eassumption.
                   * erewrite source_SomeI. eassumption. apply MInj12. eassumption.
                     apply Fwd1. eapply J1_valid; eassumption.
                     eapply Mem.perm_implies. eapply Mem.perm_max; eassumption. constructor.
                 - subst delta.
                   destruct (valid_block_dec m2 b2).
                     { subst b2; clear - v. unfold Mem.valid_block in v; xomega. }
                   erewrite source_SomeI. apply H0. assumption. apply joinI. right; split; trivial.
                   eapply Mem.perm_implies. eapply Mem.perm_max; eassumption. constructor. }
           - intros. unfold Z.divide.
             subst j12'. destruct (joinD_Some _ _ _ _ _ H) as [L12 | [L12 E12']]; clear H.
             * subst l12. destruct (local_of_ESome _ _ _ _ L12); clear L12.
               eapply MInj12. eassumption.
               red; intros. apply Fwd1. eapply J1_valid; eassumption. apply H0. eassumption.
             * specialize (MKI_range_eq _ _ _ _ _ _  Heqoutput). intros RNG.
               exploit MKI_Some12. eassumption. apply E12'. intros [E12 | [E12 [b3 [d [E' [GTb2 D]]]]]].
               ++ subst e12. destruct (extern_of_ESome _ _ _ _ E12) as [HL1 J12]; clear E12.
                  eapply MInj12. eassumption.
                  red; intros. apply Fwd1. eapply J1_valid; eassumption. apply H0. eassumption.
               ++ subst delta. exists 0. trivial.
           - intros b1 ofs b2 delta J12' mperm1'. 
             rewrite H_CONT; unfold CONT.
             subst j12'. destruct (joinD_Some _ _ _ _ _ J12') as [L12 | [L12 E12']]; clear J12'.
             * subst l12; destruct (local_of_ESome _ _ _ _ L12) as [L1b1 J12].
               rewrite <- (WDmu12 _ _ _ J12), L1b1. 
               destruct (valid_block_dec m2 b2). 2: elim n; eapply J1_valid; eassumption.  
               remember (B2 b2) as r2; symmetry in Heqr2; destruct r2; simpl.
               ++ rewrite (WDmu12 _ _ _ J12), (B2_LM _ Heqr2) in L1b1; congruence.
               ++ erewrite source_SomeI; try eassumption.
                  -- remember (j23 b2) as t. destruct t; symmetry in Heqt. destruct p.
                     ** apply inject_memval_memval_inject1.
                        intros. exploit (Mem.mi_memval _ _ _ (Mem.mi_inj _ _ _ MInj13') b1). 
                           eapply INC; unfold compose_meminj. rewrite J12, Heqt; reflexivity.
                           eassumption.
                        intros M. subst j'. rewrite H in *. inv M.
                        destruct (val_inject_split _ _ _ _ H1) as [uu [UU1 UU2]]. clear UU2.
                        destruct u; simpl in *; eexists; try reflexivity.
                        inv UU1. rewrite H3. reflexivity.
                     ** destruct UnchSrc as [UA UB UC].
                        assert (SC1: LS b1 = true /\ (compose_meminj j12 j23) b1 = None).
                        { split; trivial. unfold compose_meminj. rewrite J12, Heqt; trivial. }
                        assert (SC2: Mem.perm m1 b1 ofs Cur Readable).
                        { apply UB; trivial. eapply J1_valid; eassumption. }
                        rewrite UC; trivial.
                        eapply memval_inject_incr; [ apply MInj12; eassumption | apply INC12].
                  -- apply MInj12.
                  -- apply Fwd1. eapply J1_valid; eassumption. eapply Mem.perm_implies. eapply Mem.perm_max. eassumption. constructor.
             * destruct (ext12' _ _ _ E12') as [L1b1 L2b2]; rewrite L2b2.
               exploit MKI_Some12; try eassumption.
               intros [E12 | [E23 [b3 [d [E' [Hb2 D]]]]]].
               ++ destruct (extern_of_ESome _ _ _ _ E12) as [_ J12].
                  destruct (valid_block_dec m2 b2). 2: elim n; eapply J1_valid; eauto.
                  remember (B2 b2) as r2; symmetry in Heqr2; destruct r2; simpl.
                  ** destruct (B2valid _ Heqr2) as [_ RDOb2].
                     specialize (B2_B1 _ _ _ J12 Heqr2).
                     destruct (RDOnly_fwd1 _ B2_B1 1 ofs) as [LD Perm].
                     -- intros i I N. replace (ofs + i) with ofs in N by omega. apply Mem.perm_max in N.
                        apply (RDOb2 (ofs+delta)). eapply MInj12; eassumption.
                     -- destruct (Mem.range_perm_loadbytes m1' b1 ofs 1) as [bytes Bytes].
                        { red; intros. replace ofs0 with ofs by omega; trivial. }
                        rewrite Bytes in LD; symmetry in LD. 
                        apply loadbytes_D in LD; destruct LD as [_ LD].
                        apply loadbytes_D in Bytes; destruct Bytes as [_ Bytes].
                        destruct bytes; inversion Bytes; clear Bytes; inversion LD; clear LD.
                        rewrite <- H0, H2.
                        specialize (Perm 0); rewrite Zplus_0_r in Perm. apply Perm in mperm1'; [|omega].
                        eapply memval_inject_incr. eapply MInj12; try eassumption. assumption.
                  ** erewrite source_SomeI; try eassumption; [| apply MInj12 |].
                    -- apply inject_memval_memval_inject1. intros.
                       destruct (FE _ b2 delta J12 L1b1 ) as [b3 [d2 J23]].
                       exploit Mem.mi_memval. eapply MInj13'. 2: eassumption.
                        eapply INC; unfold compose_meminj. rewrite J12, J23; reflexivity.
                        intros MV. subst j'. rewrite H in MV. inv MV.
                        destruct (val_inject_split _ _ _ _ H1) as [uu [UU1 UU2]]. clear UU2.
                        destruct u; simpl in *; eexists; try reflexivity.
                        inv UU1. rewrite H3. reflexivity.
                    -- apply Fwd1. eapply J1_valid; eassumption. eapply Mem.perm_implies. eapply Mem.perm_max. eassumption. constructor.
               ++ subst delta.
                  destruct (valid_block_dec m2 b2). 
                  -- subst b2; clear - v; unfold Mem.valid_block in v. xomega.
                  -- clear Hb2. destruct (extern_of_ESome _ _ _ _ E') as [_ Jb1]; clear E'.
                     exploit Mem.mi_memval. apply MInj13'. eassumption. eassumption.
                     intros MV.
                     erewrite source_SomeI; try eassumption.
                     Focus 2. apply joinI. right. split; eassumption. 
                     ** apply inject_memval_memval_inject1.
                        intros ? ? ? X. rewrite X in *. inv MV.
                        destruct (val_inject_split _ _ _ _ H0) as [uu [UU1 UU2]]. clear UU2.
                        destruct u; simpl in *; eexists; try reflexivity.
                        inv UU1. rewrite H2. reflexivity.
                     ** eapply Mem.perm_implies. eapply Mem.perm_max. eassumption. constructor.
         + intros. specialize (VBj12' b).
           destruct (j12' b); trivial. destruct p. elim H. apply (VBj12' _ _ (eq_refl _)).
         + intros. unfold Mem.valid_block. (*rewrite NB2'.*) eapply VBj12'; eassumption.
         + intros. subst j12'. 
           destruct (joinD_Some _ _ _ _ _ H) as [L12 | [L12 E12']]; clear H.
           - destruct (local_of_ESome _ _ _ _ L12) as [Lb J12]; clear L12.
             eapply MInj12. eassumption. 
             destruct H0.
             left; eapply Fwd1; trivial. eapply J1_valid; eassumption. 
             right; eapply Fwd1; trivial. eapply J1_valid; eassumption.
           - exploit MKI_Some12; try eassumption. intros [E12 | [E12 [b3 [d [E' [B' D]]]]]].
             * destruct (extern_of_ESome _ _ _ _ E12).
               eapply MInj12. eassumption. 
               destruct H0.
               left; eapply Fwd1; trivial. eapply J1_valid; eassumption. 
               right; eapply Fwd1; trivial. eapply J1_valid; eassumption.
             * subst delta. destruct (extern_of_ESome _ _ _ _ E').
               exploit Mem.mi_representable.
               eapply MInj13'. eassumption. eassumption. intros [X Y]. 
               destruct (Ptrofs.unsigned_range_2 ofs); omega.
         + intros. clear H_CONT. red in FE.
           subst j12'. destruct (joinD_Some _ _ _ _ _ H) as [L12 | [L12 E12']]; clear H.
           - destruct (local_of_ESome _ _ _ _ L12) as [L1b1 J12]. 
             remember (j23 b2) as q; symmetry in Heqq.
             destruct q.
             * destruct p0. apply INC23 in Heqq.
               exploit Perm23'; try eassumption.
               intros. eapply MInj13'.
               ++ subst j'. unfold compose_meminj, join. rewrite L12, Heqq; reflexivity.
               ++ rewrite Zplus_assoc; eassumption.
             * assert (Jb1: (compose_meminj j12 j23) b1 = None).
               { unfold compose_meminj, join. rewrite J12, Heqq; trivial. }
               eapply UnchMid in H0. 
               ++ exploit Mem.mi_perm_inv. apply MInj12. eassumption. apply H0.
                  intros [P | P].
                  -- left; apply UnchSrc; eauto.
                  -- right. intros N. apply P; clear P.
                     apply UnchSrc; eauto.
               ++ rewrite <- (WDmu12 _ _ _ J12). split; trivial.
               ++ eapply J1_valid; eassumption.
           - exploit MKI_Some12; try eassumption. intros [E12 | [E12 [b [d [E' [GTb2 D]]]]]].
             * destruct (extern_of_ESome _ _ _ _ E12) as [L1b1 J12]. 
               destruct (full' _ _ _ E12') as [b3 [d2 E23']].
               destruct (ext23' _ _ _ E23') as [L2b2 L3b3].
               exploit Perm23'; try eassumption.  
               -- subst j23'. apply joinI. subst l23. rewrite local_of_Ifalse; trivial. right. split; eauto.
               -- intros. eapply MInj13'.
                  ** subst j'. unfold compose_meminj, join. rewrite L12, E12'.
                     subst j23' l23; unfold join. rewrite local_of_Ifalse, E23'; eauto.
                  ** rewrite Zplus_assoc; eassumption.
             * subst delta.
               destruct (full' _ _ _ E12') as [b3 [d2 E23']].
               rewrite HE' in E'. unfold compose_meminj in E'. rewrite E12', E23' in E'; inv E'.
               destruct (ext23' _ _ _ E23') as [L2b2 L3b3].
               exploit Perm23'; try eassumption.  
               -- subst j23'. apply joinI. subst l23. rewrite local_of_Ifalse; trivial. right. split; eauto.
               -- intros. eapply MInj13'.
                  ** unfold compose_meminj, join. rewrite L12, E12'.
                     subst j23' l23; unfold join. rewrite local_of_Ifalse, E23'; eauto.
                  ** rewrite Zplus_assoc; eassumption. }

    assert (MInj23': Mem.inject j23' m2' m3').
    { constructor.
      + constructor. assumption.
        - intros b2 b3 delta ch ofs p J23' RP. unfold Z.divide.
          destruct (joinD_Some _ _ _ _ _ J23') as [L23 | [L23 E23']]; clear J23'.
          * destruct (local_of_ESome _ _ _ _ L23).
            eapply MInj23. eassumption.
            red; intros. apply Fwd2. eapply J2_valid; eassumption. apply RP. apply H1.
          * exploit MKI_Some23; try eassumption. intros [E23 | [E23 [E' [E12 Hb1]]]].
            ++ destruct (extern_of_ESome _ _ _ _ E23).
               eapply MInj23. eassumption.
               red; intros. apply Fwd2. eapply J2_valid; eassumption. apply RP. apply H1.
            ++ rewrite Pcompare_eq_Gt in Hb1.
               destruct (extern_of_ESome _ _ _ _ E'). red in RP.
               rewrite HE' in E'.
               destruct (compose_meminjD_Some _ _ _ _ _ E') as [b1 [dd1 [d [E12' [E23'' D]]]]]; clear E'.
               subst delta. unfold mem_add_nb in NB2'.
               exploit MKI_Some12. eassumption. eassumption.
               intros [K12 | [K12 [bb3 [dd [KEE [KK DD1]]]]]]; [congruence | ].
               subst dd1. simpl in *.
               destruct (extern_of_ESome _ _ _ _ KEE) as [L1b1 Jb1]. rewrite Jb1 in H0. inversion H0; clear H0. subst bb3 dd.
               rewrite Pos.sub_add in KK. subst b2. 2: xomega. clear E23''. 
               eapply MInj13'. eassumption.
               instantiate(2:=ofs). instantiate (1:=p). clear -RP H_ACCESS Hb1 Heqoutput WDmu12 L1b1 ext12' E12' J1_valid.
               red. intros z Hz.
               unfold Mem.perm in RP. rewrite H_ACCESS in RP. unfold ACCESS in RP.
               destruct (valid_block_dec m2 b1). { clear - v Hb1. unfold Mem.valid_block in v; xomega. }
               specialize (RP _ Hz). 
               remember (source j12' m1' b1 z) as src.
               destruct src; [ | contradiction]. 
               destruct (source_SomeE _ _ _ _ _ Heqsrc) as [bb [dd [zz [HP [Hbb [KK [PP ZZ]]]]]]].
               subst p0 z.
               exploit MKI_Some12. 
               -- eassumption.
               -- subst j12'. destruct (joinD_Some _ _ _ _ _ KK) as [LOC | [LOC EXT]]; clear KK.
                  ** destruct (local_of_ESome _ _ _ _ LOC) as [L1bb J12bb]; clear LOC.
                     rewrite (WDmu12 _ _ _ J12bb) in L1bb.
                     destruct (ext12' _ _ _  E12'). congruence. 
                  ** eassumption. 
               -- intros [Ebb | [Ebb [bq [dq [Eq [Bq Dq]]]]]].
                  ** destruct (extern_of_ESome _ _ _ _ Ebb). elim n. eapply J1_valid. eassumption. 
                  ** subst dd. rewrite Bq, Pos.add_sub, Zplus_0_r. apply RP.
        - { (*mi_memval23*)
            intros b2 ofs b3 delta map23'.
            unfold Mem.perm. rewrite H_ACCESS, H_CONT; clear H_ACCESS H_CONT. 
            unfold CONT, ACCESS.
            destruct (joinD_Some _ _ _ _ _ map23') as [Loc23 | [Loc23 Ext23]].
            + destruct (local_of_ESome _ _ _ _ Loc23) as [L2b2 J23b2]; clear Loc23.
              destruct (valid_block_dec m2 b2); [| solve [elim n; eapply J2_valid; eassumption]].
              rewrite L2b2, J23b2.
              remember (B2 b2) as r2; symmetry in Heqr2; destruct r2; simpl.
              - apply B2_LM in Heqr2; congruence.
              - remember (source j12 m1 b2 ofs) as src; destruct src.
                * destruct (source_SomeE _ _ _ _ _ Heqsrc) as [b1 [d1 [zz [HP [Hb1 [J12b1 [PP ZZ]]]]]]].
                  subst. 
                  intros. rewrite <- Zplus_assoc.
                  exploit Mem.mi_memval. eapply MInj13'. 2: apply H. { apply INC; unfold compose_meminj. rewrite J12b1, J23b2; reflexivity. }
                  intros MV.
                  inv MV; try constructor.
                  apply val_inject_split in H2. destruct H2 as [u [inj12 inj23]]. simpl.
                  inv inj12; simpl; try constructor; trivial.
                  rewrite H2. econstructor; trivial.
                * destruct UnchTgt as [_ UB UC]; intros P; rewrite UC.
                  ++ eapply memval_inject_incr. apply MInj23. apply J23b2. apply P.
                     apply INC23.
                  ++ rewrite <- (WDmu23 _ _ _ J23b2). split; trivial.
                     intros b0 ? J0. destruct (compose_meminjD_Some _ _ _ _ _ J0) as [bb2 [dd1 [dd2 [K1 [K2 DD]]]]]; clear J0.
                     subst delta0. clear UB UC UnchSrc; intros P1.
                     destruct (eq_block bb2 b2).
                     -- subst bb2. rewrite K2 in J23b2. inversion J23b2; subst dd2.
                        eapply source_NoneE. eassumption. 2: apply K1. eapply J1_valid; eassumption.
                        assert (Arith: ofs + delta - (dd1 + delta) = ofs - dd1) by omega.
                        rewrite Arith in P1; assumption.
                     -- exploit Mem.mi_no_overlap. apply MInj23. apply n. eassumption. eassumption.
                        eapply MInj12; eassumption.
                        eapply Mem.perm_max. eapply Mem.perm_implies. eassumption. constructor.
                        intros [XX | XX]. elim XX; trivial. omega.
                  ++ eapply MInj23; eassumption.
            + destruct (ext23' _ _ _ Ext23) as [L2b2 L3b3]; rewrite L2b2.
              exploit MKI_Some23. eassumption. eassumption. intros [e23b2 | [e23b2 [E' [E12 GT]]]].
              - destruct (extern_of_ESome _ _ _ _ e23b2) as [_ j23b2]; rewrite j23b2.
                destruct (valid_block_dec m2 b2). 2: solve [elim n; eapply J2_valid; eassumption].
                remember (B2 b2) as r2; symmetry in Heqr2; destruct r2; simpl.
                * destruct (B2valid _ Heqr2) as [_ RDOb2]. intros RD2.
                  exploit Mem.perm_inject. apply j23b2. eassumption. apply RD2. intros RD3. 
                  destruct (RDOnly_fwd3 _ (B2_B3 _ _ _ j23b2 Heqr2) 1 (ofs+delta)) as [LD _].
                  ++ intros i I N. replace (ofs + delta + i) with (ofs+delta) in N by omega.
                     eapply MInj23 in N. 2: eassumption. destruct N as [N | N].
                     -- apply Mem.perm_max in N. apply (RDOb2 _ N).
                     -- apply N. clear - RD2. eapply Mem.perm_max. eapply Mem.perm_implies. eassumption. constructor.
                  ++ destruct (Mem.range_perm_loadbytes m3 b3 (ofs+delta) 1) as [bytes Bytes].
                     red; intros; replace ofs0 with (ofs+delta) by omega; trivial.
                     rewrite Bytes in LD. apply loadbytes_D in LD; destruct LD as [_ LD].
                     apply loadbytes_D in Bytes; destruct Bytes as [_ Bytes].
                     destruct bytes; inversion LD; inversion Bytes.
                     rewrite <- H0, H2.
                     eapply memval_inject_incr. eapply MInj23; eauto. trivial. 
                * remember (source j12 m1 b2 ofs) as src.
                  destruct src; [ | contradiction].
                  destruct (source_SomeE _ _ _ _ _ Heqsrc) as [b1 [d1 [zz [HP [Hb1 [J12b1 [PP ZZ]]]]]]].
                     subst.  
                     intros. rewrite <- Zplus_assoc.
                     exploit Mem.mi_memval. eapply MInj13'. 2: apply H. { apply INC; unfold compose_meminj. rewrite J12b1, j23b2; reflexivity. }
                     intros MV.
                     inv MV; try constructor.
                     apply val_inject_split in H2. destruct H2 as [u [inj12 inj23]]. simpl.
                     inv inj12; simpl; try constructor; trivial.
                     rewrite H2. econstructor; trivial. 
              - destruct (valid_block_dec m2 b2).
                * exfalso. clear -v GT. rewrite Pcompare_eq_Gt in GT. unfold Mem.valid_block in v; xomega. 
                * remember (source j12' m1' b2 ofs) as src. clear GT.
                  destruct src; [ | contradiction].
                  destruct (source_SomeE _ _ _ _ _ Heqsrc) as [b1 [d1 [zz [HP [Hb1 [J12b1' [PP ZZ]]]]]]].
                     subst p ofs.  
                     intros. rewrite <- Zplus_assoc.
                     exploit Mem.mi_memval. eapply MInj13'. 2: apply H. { subst j'. unfold compose_meminj. rewrite J12b1', map23'; reflexivity. }
                     intros MV.
                     inv MV; try constructor.
                     apply val_inject_split in H2. destruct H2 as [u [inj12 inj23]]. simpl.
                     inv inj12; simpl; try constructor; trivial.
                     rewrite H2. econstructor; trivial. }
      + intros b2 VB2. remember (j23' b2) as d; destruct d; trivial; symmetry in Heqd.
        elim VB2; unfold Mem.valid_block. (*rewrite NB2'.*) destruct p; eapply VBj23'; eassumption.
      + apply VBj23'.
      + { intros b2 b3 d2 b2' b3' d2' ofs ofs' NEQ j23'b2 j23'b2' Pb2 Pb2'.
          destruct (eq_block b3 b3'). 2: left; assumption. subst b3'.
          destruct (joinD_Some _ _ _ _ _ j23'b2) as [l23_b2 | [l23_b2 e23'_b2]].
          + destruct (local_of_ESome _ _ _ _ l23_b2); clear l23_b2. 
            destruct (joinD_Some _ _ _ _ _ j23'b2') as [l23_b2' | [l23_b2' e23'_b2']].
            - destruct (local_of_ESome _ _ _ _ l23_b2'); clear l23_b2'.
                 eapply MInj23; try eassumption.
                 eapply Fwd2; trivial. eapply J2_valid; eassumption.
                 eapply Fwd2; trivial. eapply J2_valid; eassumption.
            - destruct (ext23' _ _ _ e23'_b2').
              rewrite (WDmu23 _ _ _ H0) in *; congruence.
          + (*right; intros N.*)
            destruct (ext23' _ _ _ e23'_b2) as [L2b2 L3b3].
            destruct (joinD_Some _ _ _ _ _ j23'b2') as [l23_b2' | [l23_b2' e23'_b2']].
            - destruct (local_of_ESome _ _ _ _ l23_b2'); clear l23_b2'.
              rewrite (WDmu23 _ _ _ H0) in *; congruence.
            - destruct (ext23' _ _ _ e23'_b2') as [L2b2' _].
              destruct (MKI_Some23 _ _ _ _ _ _ Heqoutput _ _ _ e23'_b2) as [e23_b2 | [e23_b2 [E'b1 [e12_b1 GTb1]]]];
              destruct (MKI_Some23 _ _ _ _ _ _ Heqoutput _ _ _ e23'_b2') as [e23_b2' | [e23_b2' [E'b1' [e12_b1' GTb1']]]];
              try rewrite Pcompare_eq_Gt in *.
              * destruct (extern_of_ESome _ _ _ _ e23_b2) as [_ j23_b2].
                destruct (extern_of_ESome _ _ _ _ e23_b2') as [_ j23_b2'].
                eapply MInj23. apply NEQ. eassumption. eassumption. 
                apply Fwd2; trivial. eapply J2_valid; eassumption.
                apply Fwd2; trivial. eapply J2_valid; eassumption.
              * destruct (extern_of_ESome _ _ _ _ e23_b2) as [_ j23_b2].
                unfold Mem.perm in Pb2, Pb2'. rewrite H_ACCESS in *; clear H_ACCESS H_CONT. unfold ACCESS in *.
                destruct (valid_block_dec m2 b2). 2 : solve [ elim n; eapply J2_valid; eassumption].
                destruct (valid_block_dec m2 b2'). { clear - v0 GTb1'. unfold Mem.valid_block in v0; xomega. }
                rewrite L2b2 in *.
                remember (source j12' m1' b2' ofs') as src'.
                destruct src'; [ | contradiction].
                destruct (source_SomeE _ _ _ _ _ Heqsrc') as [b1' [d1' [zz' [HP' [Hb1' [j12'b1' [PP' ZZ']]]]]]]; clear Heqsrc'.
                subst p ofs'.
                assert (e12'_b1': e12' b1' = Some (b2', d1')).
                { destruct (joinD_Some _ _ _ _ _ j12'b1') as [LOC | [_ EXT]]; trivial.
                  destruct (local_of_ESome _ _ _ _ LOC) as [L1b1' J1].
                  rewrite (WDmu12 _ _ _ J1) in L1b1'. congruence. }
                exploit MKI_Some12. eassumption. apply e12'_b1'. intros [E12' | [E12' [bb3 [dd2' [E' [Bb2' D']]]]]].
                { destruct (extern_of_ESome _ _ _ _ E12') as [? J12'].
                  elim n. eapply J1_valid; eassumption. }
                subst d1' b2'. rewrite Pos.add_sub in *. rewrite E'b1' in E'. inversion E'; clear E'; subst bb3 dd2'.
                assert (J'b1' : j' b1' = Some (b3, d2')).
                { subst j'. unfold compose_meminj. rewrite j12'b1', j23'b2'; trivial. }
                clear Pb2'. rewrite <- Zplus_assoc; simpl.
                remember (B2 b2) as r2; symmetry in Heqr2; destruct r2; simpl in Pb2.
                ++ destruct (B2valid _ Heqr2) as [_ RDOb2]. 
                   apply (B2_B3 _ _ _ j23_b2) in Heqr2.
                   rewrite (B3sep b1' b3 d2') in Heqr2; [ congruence | | assumption ].
                   unfold compose_meminj. 
                   rewrite (join_local_extern j12 LS). subst l12 e12. unfold join. rewrite E12'.
                   remember (local_of j12 LS b1') as t; destruct t; trivial.
                   unfold local_of in Heqt. remember (LS b1') as w; destruct w; try discriminate.
                   symmetry in Heqt; destruct p; rewrite (WDmu12 _ _ _ Heqt) in Heqw.
                   rewrite (INC12 _ _ _ Heqt) in j12'b1'; inv j12'b1'. symmetry in Heqw. 
                   apply J1_valid in Heqt. congruence.
                ++ rewrite j23_b2 in Pb2.
                   remember (source j12 m1 b2 ofs) as src.
                   destruct src; [ | contradiction].
                   destruct (source_SomeE _ _ _ _ _ Heqsrc) as [b1 [d1 [zz [HP [Hb1 [j12b1 [PP ZZ]]]]]]]; clear Heqsrc.
                   subst.
                   assert (e12_b1: e12 b1 = Some (b2, d1)).
                   { rewrite <- (WDmu12 _ _ _ j12b1) in L2b2.
                     subst e12. rewrite extern_of_Ifalse; trivial. }
                   clear PP.
                   exploit Mem.mi_no_overlap. apply MInj13'. 2: eassumption. 3: eassumption. 3: apply Pb2.
                   { clear - e12_b1' e12_b1. intros N; subst b1'. congruence. }
                   { apply INC12 in j12b1.  
                     unfold compose_meminj. rewrite j12b1, j23'b2; reflexivity. }
                   rewrite Zplus_assoc. intros [X | X]. elim X; trivial. right; omega.
              * (*symmetric diagonal case*) destruct (extern_of_ESome _ _ _ _ e23_b2') as [_ j23_b2'].
                unfold Mem.perm in Pb2, Pb2'. rewrite H_ACCESS in *; clear H_ACCESS H_CONT. unfold ACCESS in *.
                destruct (valid_block_dec m2 b2'). 2 : solve [ elim n; eapply Mem.valid_block_inject_1; eassumption].
                destruct (valid_block_dec m2 b2). { clear - v0 GTb1. unfold Mem.valid_block in v0; xomega. }
                rewrite L2b2' in *.
                remember (source j12' m1' b2 ofs) as src.
                destruct src; [ | contradiction].
                destruct (source_SomeE _ _ _ _ _ Heqsrc) as [b1 [d1 [zz [HP [Hb1 [j12'b1 [PP ZZ]]]]]]]; clear Heqsrc.
                subst p ofs.
                assert (e12'_b1: e12' b1 = Some (b2, d1)).
                { destruct (joinD_Some _ _ _ _ _ j12'b1) as [LOC | [_ EXT]]; trivial.
                  destruct (local_of_ESome _ _ _ _ LOC) as [L1b1 J1].
                  rewrite (WDmu12 _ _ _ J1) in L1b1. congruence. }
                exploit MKI_Some12. eassumption. apply e12'_b1. intros [E12 | [E12 [bb3 [dd2 [E [Bb2 D]]]]]].
                { destruct (extern_of_ESome _ _ _ _ E12) as [? J12].
                  elim n. eapply Mem.valid_block_inject_2; eassumption. }
                subst d1 b2. rewrite Pos.add_sub in *. rewrite E'b1 in E. inversion E; clear E; subst bb3 dd2.
                assert (J'b1 : j' b1 = Some (b3, d2)).
                { subst j'. unfold compose_meminj. rewrite j12'b1, j23'b2; trivial. }
                clear Pb2. rewrite <- Zplus_assoc; simpl.
                remember (B2 b2') as r2; symmetry in Heqr2; destruct r2; simpl in Pb2'. 
                ++ destruct (B2valid _ Heqr2) as [_ RDOb2]. 
                   apply (B2_B3 _ _ _ j23_b2') in Heqr2. 
                   rewrite (B3sep b1 b3 d2) in Heqr2; [ congruence | | assumption ].
                   unfold compose_meminj. 
                   rewrite (join_local_extern j12 LS). subst l12 e12. unfold join. rewrite E12.
                   remember (local_of j12 LS b1) as t; destruct t; trivial.
                   unfold local_of in Heqt. remember (LS b1) as w; destruct w; try discriminate.
                   symmetry in Heqt; destruct p; rewrite (WDmu12 _ _ _ Heqt) in Heqw.
                   rewrite (INC12 _ _ _ Heqt) in j12'b1; inv j12'b1. symmetry in Heqw. 
                   apply J1_valid in Heqt. congruence.
                ++ rewrite j23_b2' in Pb2'.
                   remember (source j12 m1 b2' ofs') as src'.
                   destruct src'; [ | contradiction].
                   destruct (source_SomeE _ _ _ _ _ Heqsrc') as [b1' [d1' [zz' [HP' [Hb1' [j12b1' [PP' ZZ']]]]]]]; clear Heqsrc'.
                   subst p ofs'.
                   assert (e12_b1': e12 b1' = Some (b2', d1')).
                   { rewrite <- (WDmu12 _ _ _ j12b1') in L2b2'.
                     subst e12. rewrite extern_of_Ifalse; trivial. }
                   clear PP'.
                   exploit Mem.mi_no_overlap. apply MInj13'. 2: eassumption. 3: eassumption. 3: apply Pb2'.
                   { clear - e12_b1 e12_b1'. intros N; subst b1. congruence. }
                   { apply INC12 in j12b1'.  
                    subst j'. unfold compose_meminj. rewrite j12b1', j23'b2'; reflexivity. }
                   rewrite Zplus_assoc. intros [X | X]. elim X; trivial. right; omega.
              * destruct (extern_of_ESome _ _ _ _ E'b1) as [L1_b1 J'_b1].
                destruct (extern_of_ESome _ _ _ _ E'b1') as [L1_b1' J'_b1'].
                unfold Mem.perm in Pb2. 
                unfold Mem.perm in Pb2'. rewrite H_ACCESS in *; clear H_ACCESS H_CONT.
                unfold ACCESS in *.
                destruct (valid_block_dec m2 b2). 
                { clear - v GTb1. unfold Mem.valid_block in v; xomega. } rename n into n_b2.
                destruct (valid_block_dec m2 b2'). 
                { clear - v GTb1'. unfold Mem.valid_block in v; xomega. } rename n into n_b2'.
                remember (source j12' m1' b2 ofs) as src.
                destruct src; [ destruct p | contradiction]. 
                remember (source j12' m1' b2' ofs') as src'.
                destruct src'; [ destruct p | contradiction].
                destruct (source_SomeE _ _ _ _ _ Heqsrc) as [b1 [d1 [zz [HP [Hb1 [J12b1' [PP ZZ]]]]]]].
                inversion HP; clear HP; subst b zz ofs. 
                destruct (source_SomeE _ _ _ _ _ Heqsrc') as [b1' [d1' [zz' [HP' [Hb1' [J12b1'' [PP' ZZ']]]]]]].
                inversion HP'; clear HP'; subst b0 zz' ofs'.
                exploit Mem.mi_no_overlap. apply MInj13'. 4: apply Pb2. 4: apply Pb2'.
                ++ intros N; subst b1'. rewrite J12b1' in J12b1''. inversion J12b1''; subst b2' d1'. elim NEQ; trivial.
                ++ subst j'. unfold compose_meminj. rewrite J12b1', j23'b2; reflexivity.
                ++ subst j'. unfold compose_meminj. rewrite J12b1'', j23'b2'; reflexivity.
                ++ intros [X | X]. left; trivial. right. xomega. }
      + intros b2 b3 d2 ofs j23'_b2 P. 
        destruct (joinD_Some _ _ _ _ _ j23'_b2) as [l23_b2 | [l23_b2 e23'_b2]].
        - destruct (local_of_ESome _ _ _ _ l23_b2) as [L2_b2 j23_b2]; clear l23_b2.
          eapply MInj23. eassumption.
          unfold Mem.perm in P. rewrite H_ACCESS in P; clear H_ACCESS H_CONT. unfold ACCESS in P.
          destruct (valid_block_dec m2 b2). 2: solve[elim n; eapply J2_valid; eassumption].
          rewrite L2_b2 in P.
          remember (B2 b2) as r2; symmetry in Heqr2; destruct r2.
          * apply B2_LM in Heqr2; congruence.
          * destruct P as [P | P]; [ left | right ].
            ++ remember (source j12 m1 b2 (Ptrofs.unsigned ofs)) as src; destruct src; trivial.
               destruct (source_SomeE _ _ _ _ _ Heqsrc) as [b1 [d1 [zz [HP [Hb1 [J12b1 [PP ZZ]]]]]]].
               subst p; rewrite ZZ. eapply Mem.perm_inject. apply J12b1. apply MInj12. eassumption.
            ++ remember (source j12 m1 b2 (Ptrofs.unsigned ofs-1)) as src; destruct src; trivial.
               destruct (source_SomeE _ _ _ _ _ Heqsrc) as [b1 [d1 [zz [HP [Hb1 [J12b1 [PP ZZ]]]]]]].
               subst p; rewrite ZZ. eapply Mem.perm_inject. apply J12b1. apply MInj12. eassumption.
        - exploit MKI_Some23. eassumption. eassumption. intros [e23_b2 | [e23_b2 [E' [e12_b1 GT1]]]].
          * destruct (extern_of_ESome _ _ _ _ e23_b2) as [L2_b2 j23_b2].
            unfold Mem.perm in P. rewrite H_ACCESS in P; clear H_ACCESS H_CONT. unfold ACCESS in P.
            destruct (valid_block_dec m2 b2). 2: solve[ elim n; eapply J2_valid; eassumption].
            rewrite L2_b2, j23_b2 in P.
            remember (B2 b2) as r2; symmetry in Heqr2; destruct r2.
            ++ eapply MInj23; eassumption.
            ++ eapply MInj23. eassumption.
               destruct P as [P | P] ; [ left | right ].
               -- remember (source j12 m1 b2 (Ptrofs.unsigned ofs)) as src; destruct src; try contradiction.
                  destruct (source_SomeE _ _ _ _ _ Heqsrc) as [b1 [d1 [zz [HP [Hb1 [J12b1 [PP ZZ]]]]]]].
                  rewrite ZZ. eapply Mem.perm_inject. apply J12b1. apply MInj12. eassumption.
               -- remember (source j12 m1 b2 (Ptrofs.unsigned ofs-1)) as src; destruct src; try contradiction.
                  destruct (source_SomeE _ _ _ _ _ Heqsrc) as [b1 [d1 [zz [HP [Hb1 [J12b1 [PP ZZ]]]]]]].
                  rewrite ZZ. eapply Mem.perm_inject. apply J12b1. apply MInj12. eassumption.
          * rewrite Pcompare_eq_Gt in *.
            unfold Mem.perm in P. rewrite H_ACCESS in *; clear H_ACCESS H_CONT. unfold ACCESS in *.
            destruct (valid_block_dec m2 b2). 
            { clear - v GT1. unfold Mem.valid_block in v; xomega. } rename n into n_b2.
            destruct (extern_of_ESome _ _ _ _ E') as [L1_b1 J'_b1].
            destruct P as [P | P].
            ++ remember (source j12' m1' b2 (Ptrofs.unsigned ofs)) as src; destruct src. 2: contradiction.
               destruct (source_SomeE _ _ _ _ _ Heqsrc) as [b1 [d1 [zz [HP [Hb1 [J12b1 [PP ZZ]]]]]]]; subst p.
               subst j12'. destruct (joinD_Some _ _ _ _ _ J12b1) as [l12_b1 | [l12_b1 e12'b1]].
               -- destruct (local_of_ESome _ _ _ _ l12_b1).
                  rewrite (WDmu12 _ _ _ H0) in H.
                  destruct (ext23' _ _ _ e23'_b2) as [EE _]; congruence.
               -- exploit MKI_Some12. eassumption. apply e12'b1. intros [e12b1 | [e12b1 [bb [dd [EE' [Bb2 DD]]]]]].
                  ** destruct (extern_of_ESome _ _ _ _ e12b1). elim n_b2. eapply J1_valid. eassumption.
                  ** subst d1. rewrite Zplus_0_r, ZZ in *. 
                     assert (j' b1 = Some (b3, d2)). { subst j'. unfold compose_meminj. rewrite J12b1, j23'_b2; trivial. }
                     exploit Mem.mi_representable. apply MInj13'. apply H.
                     left. instantiate (1:=ofs). rewrite ZZ; assumption. rewrite ZZ; trivial.
            ++ remember (source j12' m1' b2 (Ptrofs.unsigned ofs-1)) as src; destruct src. 2: contradiction.
               destruct (source_SomeE _ _ _ _ _ Heqsrc) as [b1 [d1 [zz [HP [Hb1 [J12b1 [PP ZZ]]]]]]]; subst p.
               subst j12'. destruct (joinD_Some _ _ _ _ _ J12b1) as [l12_b1 | [l12_b1 e12'b1]].
               -- destruct (local_of_ESome _ _ _ _ l12_b1).
                  rewrite (WDmu12 _ _ _ H0) in H.
                  destruct (ext23' _ _ _ e23'_b2) as [EE _]; congruence.
               -- exploit MKI_Some12. eassumption. apply e12'b1. intros [e12b1 | [e12b1 [bb [dd [EE' [Bb2 DD]]]]]].
                  ** destruct (extern_of_ESome _ _ _ _ e12b1). elim n_b2. eapply J1_valid. eassumption.
                  ** subst d1. rewrite Zplus_0_r, ZZ in *. 
                     assert (j' b1 = Some (b3, d2)). { subst j'. unfold compose_meminj. rewrite J12b1, j23'_b2; trivial. }
                     exploit Mem.mi_representable. apply MInj13'. apply H.
                     right. instantiate (1:=ofs). rewrite ZZ; assumption. trivial.
      + intros b2 ofs b3 d2 k p j23'_b2 P. 
        destruct (joinD_Some _ _ _ _ _ j23'_b2) as [l23_b2 | [l23_b2 e23'_b2]].
        - destruct (local_of_ESome _ _ _ _ l23_b2) as [L2_b2 j23_b2]; clear l23_b2.
          unfold Mem.perm. rewrite H_ACCESS; clear H_ACCESS H_CONT. unfold ACCESS.
          destruct (valid_block_dec m2 b2). 2: solve[elim n; eapply J2_valid; eassumption].
          rewrite L2_b2.
          remember (B2 b2) as r2; symmetry in Heqr2; destruct r2.
          * apply B2_LM in Heqr2; congruence.
          *  remember (source j12 m1 b2 ofs) as src; destruct src. 
            ++ destruct p0. destruct (source_SomeE _ _ _ _ _ Heqsrc) as [b1 [d1 [zz [HP [Hb1 [J12b1 [PP ZZ]]]]]]].
               inv HP. rewrite <- Zplus_assoc in P.
               eapply MInj13'. 2: apply P. eapply INC12 in J12b1. unfold compose_meminj. rewrite J12b1, j23'_b2; trivial.
            ++ assert (vb3: Mem.valid_block m3 b3) by (eapply J2_valid; eassumption).
               destruct (Mem.perm_dec m2 b2 ofs Max Nonempty). 2: right; trivial. 
               apply UnchTgt in P; trivial.
               -- eapply MInj23; eassumption.
               -- clear P. clear H H0. rewrite <- (WDmu23 _ _ _ j23_b2). split; trivial. clear Perm23' UnchMid UnchSrc12.
                  red; intros b1 ? J0. intros N. destruct (compose_meminjD_Some _ _ _ _ _ J0) as [bb2 [dd1 [dd2 [K1 [K2 DD]]]]]; clear J0.
                  assert (vb1: Mem.valid_block m1 b1) by (eapply J1_valid; eassumption). 
                  destruct (eq_block bb2 b2); subst.
                  ** apply (source_NoneE _ _ _ _ Heqsrc _ _ vb1 K1).
                     rewrite K2 in j23_b2; inv j23_b2.
                     assert (Arith: ofs + d2 - (dd1 + d2) = ofs - dd1) by omega.
                     rewrite Arith in *; trivial.
                  ** clear Heqoutput HE' INC local_jj' UnchSrc UnchTgt.
                     exploit Mem.perm_inject. apply K1. apply MInj12. apply N. intros P'.
                     exploit Mem.mi_no_overlap. apply MInj23. apply n. eassumption. eassumption. eassumption. eassumption.
                     intros [X | X]. elim X; trivial. omega.
        - destruct (ext23' _ _ _ e23'_b2) as [L2_b2 L3_b3].
          exploit MKI_Some23. eassumption. eassumption. intros [e23_b2 | [e23_b2 [e'_b1 [e12_b1 GT]]]].
          * destruct (extern_of_ESome _ _ _ _ e23_b2) as [_ j23_b2].
            assert (Mem.valid_block m2 b2 /\ Mem.valid_block m3 b3) by (eapply J2_valid; eassumption).
            destruct H as [vb2 vb3].   
            unfold Mem.perm. rewrite H_ACCESS; clear H_ACCESS H_CONT. unfold ACCESS.
            destruct (valid_block_dec m2 b2); try contradiction.
            rewrite L2_b2, j23_b2; clear v.
            remember (B2 b2) as r2; symmetry in Heqr2; destruct r2.
            ++ destruct (Mem.perm_dec m2 b2 ofs Max Nonempty); [ | right; trivial].
               destruct (B2valid _ Heqr2) as [_ RDOb2]. 
               destruct (RDOnly_fwd3 _ (B2_B3 _ _ _ j23_b2 Heqr2) 1 (ofs+d2)) as [_ P3].
                  ** intros i I N. replace (ofs + d2 + i) with (ofs+d2) in N by omega.
                     eapply MInj23 in N. 2: eassumption. destruct N as [N | N].
                     -- apply Mem.perm_max in N. apply (RDOb2 _ N).
                     -- congruence.
                  ** specialize (P3 0); rewrite Zplus_0_r in P3. apply P3 in P; [ | omega].
                     eapply MInj23 in P; eassumption.
            ++ remember (source j12 m1 b2 ofs) as src.
               destruct src. 2:solve [right; intros N; apply N].
               destruct (source_SomeE _ _ _ _ _ Heqsrc) as [b1 [d1 [zz [HP [Hb1 [J12b1 [PP ZZ]]]]]]]; subst p0 ofs.
               apply INC12 in J12b1.
               eapply MInj13'. 
               -- subst j'. unfold compose_meminj. rewrite J12b1, j23'_b2; reflexivity.
               -- rewrite Zplus_assoc; trivial.
          * destruct (extern_of_ESome _ _ _ _ e'_b1) as [L1_b1 j'_b1]. 
            rewrite Pcompare_eq_Gt in GT.
            unfold Mem.perm. rewrite H_ACCESS; clear H_ACCESS H_CONT. unfold ACCESS.
            destruct (valid_block_dec m2 b2). { exfalso. clear - v GT. unfold Mem.valid_block in v; xomega. }
            remember (source j12' m1' b2 ofs) as src.
            destruct src. 2:solve [right; intros N; apply N].
            destruct (source_SomeE _ _ _ _ _ Heqsrc) as [b1 [d1 [zz [HP [Hb1 [J12b1 [PP ZZ]]]]]]]; subst p0 ofs.
            eapply MInj13'. 
               -- subst j'. unfold compose_meminj. rewrite J12b1, j23'_b2; reflexivity.
               -- rewrite Zplus_assoc; trivial. }

  intuition. 
(*assert X:  (forall b2 b3 d (J2': j2' b2 = Some (b3, d)),
     j2 b2 = Some (b3, d) \/
     j2 b2 = None /\ j' (b2 - (Mem.nextblock m2))%positive = Some (b3, d) /\ 
                     (compose_meminj j1 j2) ((b2 - (Mem.nextblock m2))%positive) = None /\ 
                     (~ Mem.valid_block m2 b2)).*)
remember (j23 b2) as t; symmetry in Heqt; destruct t; [ left | right; split; trivial].
  destruct p; rewrite (INC23 _ _ _ Heqt) in J2'; inv J2'; trivial.
destruct (Esep2' _ _ _ Heqt J2'). destruct E_INC23 as [Inc23a Inc23b].
subst j23' l23.
rewrite (join_local_extern _ LM) in Heqt. rewrite Inc23b in Heqt.
apply joinD_None in Heqt. destruct Heqt.
apply joinD_Some in J2'. destruct J2' as [? | [_ E23']]. congruence.
destruct (MKI_Some23 _ _ _ _ _ _ Heqoutput _ _ _ E23') as [ES | [EN [E' [E12 GT]]]]. subst e23; congruence. 
specialize (MKI_Some12 _ _ _ _ _ _ Heqoutput ((b2 - Mem.nextblock m2)%positive)); intros.
subst e'. unfold extern_of in E'. 
remember (LS (b2 - Mem.nextblock m2)%positive) as q; symmetry in Heqq.
destruct q; [ congruence | ]. subst sizeM2.
split. 
- rewrite J' in *; clear J'. apply compose_meminjD_Some in E'.
  destruct E' as [bb2 [dd1 [dd2 [JJ1 [JJ2 DD]]]]].
  subst j12' l12. unfold join, local_of in JJ1. rewrite Heqq in JJ1.
  destruct (H3 _ _ JJ1) as [? | [? [bb [dd [E [B D]]]]]]; clear H3. congruence.
  unfold join, local_of; rewrite Heqq, JJ1; subst; f_equal; f_equal. clear -GT.
  apply Pos.sub_add. apply Pos.compare_gt_iff in GT; trivial. 
- rewrite (join_local_extern j12 LS). unfold join, local_of; subst e12; simpl.
  split; [trivial | split; [unfold compose_meminj| trivial]].
  rewrite Heqq, E12; trivial.
Qed.

Lemma interp_II 
      (ret1 ret3: val) tp (HasType1 : Val.has_type ret1 tp) (HasType3 : Val.has_type ret3 tp)
      (RVinj : val_inject j' ret1 ret3):
exists (j1' j2' : meminj) (m2' : mem) (ret2 : val),
  inject_incr j1 j1' /\ esep m1 j1 j1' m2 LM /\(forall b1 b2 d, j1' b1 = Some(b2,d) -> Mem.valid_block m1' b1 /\ Mem.valid_block m2' b2) /\
  inject_incr j2 j2' /\ esep m2 j2 j2' m3 LT /\ (forall b1 b2 d, j2' b1 = Some(b2,d) -> Mem.valid_block m2' b1 /\ Mem.valid_block m3' b2) /\
  full_ext LS j1' j2' /\ j' = compose_meminj j1' j2' /\
  Mem.inject j1' m1' m2' /\ Mem.inject j2' m2' m3' /\
  Val.has_type ret2 tp /\
  val_inject j1' ret1 ret2 /\ val_inject j2' ret2 ret3 /\
  mem_forward m2 m2' /\ RDOnly_fwd m2 m2' B2 /\
  Mem.unchanged_on
    (fun (b : block) (z : Z) => LM b = true /\ loc_out_of_reach j1 m1 b z) m2 m2' /\
  Mem.unchanged_on (fun (b : block) (_ : Z) => LM b = true /\ j2 b = None) m2 m2' /\
  (forall b2 b3 d (J2': j2' b2 = Some (b3, d)),
     j2 b2 = Some (b3, d) \/
     j2 b2 = None /\ j1' (b2 - (Mem.nextblock m2))%positive = Some (b2, 0) /\
                     j' (b2 - (Mem.nextblock m2))%positive = Some (b3, d) /\ 
                     (compose_meminj j1 j2) ((b2 - (Mem.nextblock m2))%positive) = None /\ 
                     (~ Mem.valid_block m2 b2)).
Proof. intros.
destruct interp_II_mem_only as [j1' [j2' [m2' [X1 [X2 [X3 [X4 [X5 [X6 
  [X7 [X8 [X9 [X10 [X11 [X12 [X13 [X14 X15]]]]]]]]]]]]]]]]]; trivial.


  rewrite X8 in RVinj; destruct (val_inject_split _ _ j1' j2' RVinj) as [ret2 [RVinj12 RVinj23]].
  assert (HasType2: Val.has_type ret2 tp).
  { subst. clear - RVinj12 RVinj23 HasType1 HasType3.
    inv RVinj23; simpl; trivial. }
  exists j1', j2', m2', ret2; intuition.
Qed.
End Interpolation_II.