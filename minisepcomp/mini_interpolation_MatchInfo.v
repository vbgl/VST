Require Import Events.
Require Import Memory.
Require Import Coqlib.
Require Import Values.
Require Import Maps.
Require Import Integers.
Require Import AST.
Require Import Globalenvs.
Require Import Axioms.

Require Import sepcomp.mem_lemmas. (*needed for definition of mem_forward etc*)
(*Require Import sepcomp.semantics.
Require Import sepcomp.semantics_lemmas.*)
(*
Require Import structured_injections.
Require Import reach.*)
(*Require Import sepcomp.effect_semantics.*)

Require Import msl.Axioms. (*for extensionality*)

Require Import minisepcomp.mini_simulations_MatchInfo.
Require Import minisepcomp.mini_simulations_lemmas_MatchInfo.
Require Import minisepcomp.mem_interpolation_defs.
Require Import minisepcomp.interpolation_memory. 
Require Import minisepcomp.BuiltinEffects. 


Lemma meminj_no_overlap_rcni j k m (M:Mem.meminj_no_overlap j m)
   (I: inject_incr k j): Mem.meminj_no_overlap k m.
Proof. red; intros. apply I in H0. apply I in H1. eapply M; eauto. Qed.

Lemma inject_incr_extern_of j L: inject_incr (extern_of j L) j.
Proof. red; intros. apply (extern_of_ESome _ _ _ _ H). Qed.
Lemma inject_incr_local_of j L: inject_incr (local_of j L) j.
Proof. red; intros. apply (local_of_ESome _ _ _ _ H). Qed.

Lemma interp_II: forall m1 m2 j12 (L1 L2 L3: block -> bool) M1 M2 M3
                             (MInj12 : Mem.inject j12 m1 m2) m1'
                             (Fwd1: mem_forward m1 m1') j23 m3
                             (MInj23 : Mem.inject j23 m2 m3) m3'
                             (Fwd3: mem_forward m3 m3')
                              j' j (J: j = compose_meminj j12 j23)
                             (SMvalNu' : meminj_valid j' (M1,L1) (M3,L3) m1' m3')
                             (MemInjNu' : Mem.inject  j' m1' m3')
                             
                             (ExtIncr: mini_extern_incr j j' L1 L3)
                             (*Pure: pure_comp_ext j12 j23 m1 m2*)
                             (WDmu12 : forall (b1 b2 : block) (d : Z), j12 b1 = Some (b2, d) -> L1 b1 = L2 b2)
                             (WDmu23 : forall (b1 b2 : block) (d : Z), j23 b1 = Some (b2, d) -> L2 b1 = L3 b2)
                             (WDmu : forall (b1 b2 : block) (d0 : Z), j b1 = Some (b2, d0) -> L1 b1 = L3 b2)
                             (mu12_valid : meminj_valid j12 (M1,L1) (M2,L2) m1 m2)
                             (mu23_valid : meminj_valid j23 (M2,L2) (M3,L3) m2 m3)

                             (UnchSrc : Mem.unchanged_on (fun b1 z => L1 b1 = true /\ j b1 = None) m1 m1')
                             (UnchTgt : Mem.unchanged_on (o_o_reach j L3 m1) m3 m3')
(*
                             (Norm12: forall b1 b2 d1, extern_of j12 b1 = Some(b2,d1) ->
                                             exists b3 d2, extern_of j23 b2 = Some(b3, d2))*)
                             (full: full_ext j12 j23 L1 L2)

         B1 B2 B3 (*(RDOnly12: RDOnly_inj m1 m2 j12 B)*)
          
          (*(RDOnly23: RDOnly_inj m2 m3 j23 B) temporarily -- weakened to the following*) (*readonly blocks are not local*)

           (RDOnly_fwd1: RDOnly_fwd m1 m1' B1) (RDOnly_fwd3: RDOnly_fwd m3 m3' B3)
           (HB3: forall b3, B3 b3 = true -> L3 b3 = false)
           (B1_B2: forall b1, B1 b1 = true -> exists b2 d1, j12 b1 = Some (b2, d1) /\ B2 b2 = true)
           (B2_B3: forall b2, B2 b2 = true -> exists b3 d2, j23 b2 = Some (b3, d2) /\ B3 b3 = true)
(*           (BSep : forall (b1 b2 : block) (d : Z),
                 as_inj (compose_sm j12 j23) b1 = None ->
                 as_inj j' b1 = Some (b2, d) -> B b2 = false)
GSep : globals_separate g3 j j'
MRR1 : mem_respects_readonly g1 m1
MRR2 : mem_respects_readonly g2 m2
MRR3 : mem_respects_readonly g3 m3*)
,
exists m2', exists j12', exists j23', j'=compose_meminj j12' j23' /\
                             mini_extern_incr j12 j12' L1 L2 /\ mini_extern_incr j23 j23' L2 L3 /\
                             meminj_valid j12' (M1,L1) (M2,L2) m1' m2' /\ meminj_valid j23' (M2,L2) (M3,L3) m2' m3' /\
                             Mem.inject j12' m1' m2' /\ mem_forward m2 m2' /\ Mem.inject j23' m2' m3' /\
                             full_ext j12' j23' L1 L2 /\ RDOnly_fwd m2 m2' B2 /\
                             (*inject_separated j12 j12' m1 m2 /\ inject_separated j23 j23' m2 m3 /\*)
                             Mem.unchanged_on (o_o_reach j12 L2 m1) m2 m2' /\
                             Mem.unchanged_on (fun b2 z => L2 b2 = true /\ j23 b2 = None) m2 m2' 
(*/\                              (forall b1 b2 d, extern_of j12' b1 = Some (b2, d) ->
                                               extern_of j12 b1 = Some (b2, d) \/
                                               extern_of j12 b1 = None /\
                                               exists b3 d2, extern_of j' b1 = Some (b3, d2)) /\
                              (forall b2 b3 d2, extern_of j23' b2 = Some (b3, d2) ->
                                               extern_of j23 b2 = Some (b3, d2) \/
                                               extern_of j23 b2 = None /\
                                               exists b1 d, extern_of j12' b1 = Some (b2, d))*).
Proof. intros.
  assert (HB2: forall b2, B2 b2 = true -> L2 b2 = false).
  { intros. destruct (B2_B3 _ H) as [b3 [? [? ?]]]. 
    apply HB3 in H1. rewrite (WDmu23 _ _ _ H0); trivial. }
  assert (HB1: forall b1, B1 b1 = true -> L1 b1 = false).
  { intros. destruct (B1_B2 _ H) as [b2 [? [? ?]]]. 
    apply HB2 in H1. rewrite (WDmu12 _ _ _ H0); trivial. }
  set (extern_of j12 L1) as e12 in *;
  set (extern_of j23 L2) as e23 in *;
  set (extern_of j' L1) as e' in *;
  set (local_of j12 L1) as l12 in *;
  set (local_of j23 L2) as l23 in *;
  set (local_of j' L1) as l' in *;
  set (Mem.nextblock m2) as sizeM2 in *.
  remember (mkInjections (Mem.nextblock m2) e12 e23 e') as output.
  destruct output as [e12' e23'].
  set (j12' := join l12 e12') in *.
  set (j23' := join l23 e23') in *.
  
  assert (extern_of_e12': is_extern e12' L1).
  { red; unfold extern_of. extensionality b. remember (e12' b) as d.
    destruct d. 2: destruct (L1 b); trivial. destruct p; symmetry in Heqd.
    destruct (MKI_Some12 _ _ _ _ _ _ Heqoutput _ _ _ Heqd) as [E12 | [E12 [b3 [d [E' [BB D]]]]]].
    + destruct (extern_of_ESome _ _ _ _ E12) as [HL _]; rewrite HL; trivial.
    + subst z e'. destruct (extern_of_ESome _ _ _ _ E') as [HL _]; rewrite HL; trivial.
  }
  assert (ext12': forall b1 b2 d, e12' b1 = Some (b2,d) -> L1 b1 = false /\ L2 b2 = false).
  { intros. exploit MKI_Some12. eassumption. eassumption.
    intros [E12 | [E12 [b [dd [E' [BB2 D]]]]]].
    + subst e12. destruct (extern_of_ESome _ _ _ _ E12); clear E12. split; trivial. rewrite <- (WDmu12 _ _ _ H1); trivial.
    + subst d e'. destruct (extern_of_ESome _ _ _ _ E'); clear E'. split; trivial.
      remember (L2 b2) as q; destruct q; trivial. symmetry in Heqq.
      eapply mu12_valid in Heqq. subst b2. unfold Mem.valid_block in Heqq. xomega. }
  
  assert (local_of_e12': local_of e12' L1 = (fun b => None)).
  { unfold local_of. extensionality b. remember (L1 b) as q.
    destruct q; trivial. 
    remember (e12' b) as d. destruct d; trivial. symmetry in Heqd; destruct p. 
    destruct (MKI_Some12 _ _ _ _ _ _ Heqoutput _ _ _ Heqd) as [E12 | [E12 [b3 [d [E' [BB D]]]]]].
    + destruct (extern_of_ESome _ _ _ _ E12) as [HL _]; congruence. 
    + subst z e'. destruct (extern_of_ESome _ _ _ _ E') as [HL _]; congruence. 
  }
  assert (INC12: extern_incr j12 j12' L1).
  { split. 
    + subst j12' l12. rewrite extern_of_join_local_x, extern_of_e12'.
      eapply MKI_incr12. apply  Heqoutput.
    + subst j12' l12. rewrite local_of_join_local_x, local_of_e12', join_None_rightneutral; trivial. }

  assert (extern_of_e23': is_extern e23' L2).
  { red; unfold extern_of. extensionality b. remember (L2 b) as q.
    destruct q; trivial. symmetry in Heqq.
    remember (e23' b) as d. destruct d; trivial. destruct p; symmetry in Heqd.
    destruct (MKI_Some23 _ _ _ _ _ _ Heqoutput _ _ _ Heqd) as [E23 | [E23 [E' [E12 X]]]].
    + destruct (extern_of_ESome _ _ _ _ E23) as [HL _]; congruence. 
    + assert (VB: Mem.valid_block m2 b) by (apply mu12_valid; trivial).
      clear - VB X. unfold Mem.valid_block in VB. rewrite Pcompare_eq_Gt in X. xomega. }


  assert (ext23': forall b2 b3 d, e23' b2 = Some (b3,d) -> L2 b2 = false /\ L3 b3 = false).
  { intros. exploit MKI_Some23. eassumption. eassumption.
    intros [E23 | [E23 [E' [E12 BB2]]]].
    + subst e23. destruct (extern_of_ESome _ _ _ _ E23); clear E23. split; trivial. rewrite <- (WDmu23 _ _ _ H1); trivial.
    + subst e'. rewrite Pcompare_eq_Gt in BB2.
      destruct (extern_of_ESome _ _ _ _ E'); clear E'.
      split.
      - remember (L2 b2) as q; destruct q; trivial. symmetry in Heqq.
        eapply mu12_valid in Heqq. clear - BB2 Heqq. unfold Mem.valid_block in Heqq. xomega.
      - remember (L3 b3) as q; destruct q; trivial. symmetry in Heqq. exfalso.
        destruct ExtIncr as [EIa EIb].
        destruct (EIb (b2 - Mem.nextblock m2) b3 d)%positive; trivial; try congruence.
        subst j. unfold compose_meminj.
          remember (j12 (b2 - Mem.nextblock m2)%positive) as t.
          destruct t; trivial. symmetry in Heqt; exfalso; destruct p.
          rewrite (join_local_extern j12 L1) in Heqt.
          destruct (joinD_Some _ _ _ _ _ Heqt) as [LL | [LL EE]].
          ++ destruct (local_of_ESome _ _ _ _ LL); congruence.
          ++ subst e12. rewrite E12 in EE; discriminate. }

  assert (local_of_e23': local_of e23' L2 = (fun b => None)).
  { unfold local_of. extensionality b. remember (L2 b) as q.
    destruct q; trivial. symmetry in Heqq.
    remember (e23' b) as d. destruct d; trivial. symmetry in Heqd; destruct p. 
    destruct (MKI_Some23 _ _ _ _ _ _ Heqoutput _ _ _ Heqd) as [E23 | [E23 [E' [E12 X]]]].
    + destruct (extern_of_ESome _ _ _ _ E23) as [HL _]; congruence. 
    + assert (VB: Mem.valid_block m2 b) by (apply mu12_valid; trivial).
      clear - VB X. unfold Mem.valid_block in VB. rewrite Pcompare_eq_Gt in X. xomega. } 

  assert (INC23: extern_incr j23 j23' L2).
  { split. 
    + subst j23' l23. rewrite extern_of_join_local_x, extern_of_e23'.
      eapply MKI_incr23. apply  Heqoutput.
    + subst j23' l23. rewrite local_of_join_local_x, local_of_e23', join_None_rightneutral; trivial. }

  assert (full' : full_comp e12' e23').
  { eapply MKI_norm. 3: eassumption.
    + intros b1 b2 d1 E12. subst e12 e23. destruct (extern_of_ESome _ _ _ _ E12) as [HL1 J12].
      destruct (full _ _ _ HL1 J12) as [HL2 [b3 [d2 J23]]].
      exists b3, d2. rewrite extern_of_Ifalse; trivial.
    + intros b2 [b3 d2] E23. subst e23. 
      destruct (extern_of_ESome _ _ _ _ E23) as [HL2 J23].
      eapply (Mem.valid_block_inject_1 j23); eassumption. }

   assert (local_jj': local_of j' L1 = local_of j L1).
   { destruct ExtIncr as [EIa EIb]. extensionality b.
         unfold local_of. remember (L1 b) as d. destruct d; trivial.
         remember (j b) as q.
         destruct q; symmetry in Heqq.
         + destruct p; apply EIa; trivial.
         + remember (j' b) as w.
           destruct w; trivial; symmetry in Heqw.
           destruct p. destruct (EIb _ _ _ Heqq Heqw). congruence. }

  assert (MiniINC12: mini_extern_incr j12 j12' L1 L2).
  { split. 
    + rewrite (join_local_extern j12 L1).
      red; intros. apply joinI. destruct (joinD_Some _ _ _ _ _ H) as [HL | [HL HE]]; clear H.
      - subst j12' l12. left; trivial.
      - subst l12. rewrite <- extern_of_e12'. right. 
        split; trivial. destruct INC12 as [I12a I12b].
        apply I12a in HE.  subst j12'. rewrite extern_of_join_local_x in HE; trivial.
    + subst j12' l12. intros. destruct (joinD_Some _ _ _ _ _ J') as [HL | [HL HE12']]; clear J'.
      - destruct (local_of_ESome _ _ _ _ HL). congruence.
      - rewrite <- extern_of_e12' in HE12'.
        destruct (extern_of_ESome _ _ _ _ HE12'). split; trivial.
        destruct (full' _ _ _ H0) as [b3 [d2 E23']]. 
        rewrite <- extern_of_e23' in E23'.
        apply (extern_of_ESome _ _ _ _ E23'). }

  assert (MiniINC23: mini_extern_incr j23 j23' L2 L3).
  { split. 
    + rewrite (join_local_extern j23 L2).
      red; intros. apply joinI. destruct (joinD_Some _ _ _ _ _ H) as [HL23 | [HL23 HE23]]; clear H.
      - subst l23. left; trivial.
      - right. subst l23. split; trivial. 
        destruct INC23 as [I23a I23b].
        apply I23a in HE23. subst j23'. rewrite extern_of_join_local_x, extern_of_e23' in HE23; trivial.
    + subst j12' l12. intros. destruct (joinD_Some _ _ _ _ _ J') as [HL23 | [HL23 HE23']]; clear J'.
      - destruct (local_of_ESome _ _ _ _ HL23). congruence.
      - rewrite <- extern_of_e23' in HE23'.
        destruct (extern_of_ESome _ _ _ _ HE23'). split; trivial.
        exploit MKI_Some23'. eassumption. eassumption. intros [E23 | [b E']].
        * subst e23. destruct (extern_of_ESome _ _ _ _ E23). rewrite <- (WDmu23 _ _ _ H2); trivial.
        * subst e'.
          destruct (extern_of_ESome _ _ _ _ E'); clear E'. destruct ExtIncr as [EIa EIb].
          remember (j b) as q.
          destruct q; symmetry in Heqq.
          ++ destruct p. rewrite (EIa _ _ _ Heqq) in H2. inv H2.
             rewrite <- (WDmu _ _ _ Heqq); trivial.
          ++ apply (EIb _ _ _ Heqq H2). }
  assert (HE': e' = compose_meminj e12' e23').
  { eapply MKIcomposition. 4: symmetry; eassumption.
     + red; intros b1 b2 d1 E12. subst e12 e23. 
       destruct (extern_of_ESome _ _ _ _ E12) as [X1 X2]; clear E12.
       destruct (full _ _ _ X1 X2) as [HL2 [b3 [d2 E23]]].
       rewrite extern_of_Ifalse; trivial. exists b3, d2; trivial.
     + subst e12 e23 e'. intros b1 b3 d E123.
       destruct ExtIncr as [EIa EIb].
       rewrite compose_meminj_extern in E123; trivial.
       destruct (extern_of_ESome _ _ _ _ E123) as [X1 X2]; clear E123.
       subst j. apply EIa in X2. rewrite extern_of_Ifalse; trivial.
     + intros b2 (b3, d2) E23. destruct (extern_of_ESome _ _ _ _ E23) as [X1 X2]; clear E23.
       eapply Mem.valid_block_inject_1; eassumption.
  }
  assert (J': j' = compose_meminj j12' j23').
  { clear Heqoutput. rewrite (join_local_extern j' L1); subst e' j12' j23'.
       subst l12 l23. rewrite HE', local_jj'. subst j.
       erewrite <- compose_meminj_local. 2: apply WDmu12. 
       apply compose_meminj_join.
       - rewrite <- extern_of_e12'. eapply disjoint_local_extern.
       - intros. rewrite <- extern_of_e23'. apply extern_of_Itrue.
         destruct (local_of_ESome _ _ _ _ H) as [HL J12].
         rewrite <- (WDmu12 _ _ _ J12); trivial.
       - intros. destruct (full' _ _ _ H) as [b3 [d2 E23']]. apply local_of_Ifalse.
         rewrite <- extern_of_e23' in E23'.
         apply (extern_of_ESome _ _ _ _ E23'). }
  
  assert (FE: full_ext j12' j23' L1 L2).
  { red; intros. red in full.
    remember (j12 b1) as d.
    destruct d; symmetry in Heqd.
    + destruct p. destruct (full _ _ _ H Heqd) as [HL2 [b3 [d2 J23]]].
      apply MiniINC12 in Heqd. rewrite Heqd in H0. inv H0. 
      split; trivial. apply MiniINC23 in J23. exists b3, d2; trivial.
    + destruct MiniINC12 as [MI12a MI12b]. destruct (MI12b _ _ _ Heqd H0).
      split; trivial. subst j12' l12. destruct (joinD_Some _ _ _ _ _ H0) as [HL12 | [HL12 HE12']]; clear H0.
      - destruct (local_of_ESome _ _ _ _ HL12); congruence.
      - apply full' in HE12'. destruct HE12' as [b3 [d2 HE12]]. subst j23'.
        exists b3, d2. apply joinI. right. split; trivial.
        subst l23. remember (local_of j23 L2 b2) as q.
        destruct q; trivial; symmetry in Heqq.
        destruct p. destruct (local_of_ESome _ _ _ _ Heqq); congruence. }

  assert (VBj12: meminj_validblock_2 j12 m2).
  { red; intros. eapply Mem.valid_block_inject_2; eassumption. }

  assert (VBj12': forall b1 b2 d1 (J12': j12' b1 = Some(b2,d1)),
           Mem.valid_block m1' b1 /\ Plt b2 (mem_add_nb m1' m2)).
  { intros. unfold mem_add_nb. destruct mu12_valid as [VAL1 [VAL2 [VAL3 [VAL4 VAL5]]]].
    subst j12'. destruct (joinD_Some _ _ _ _ _ J12') as [LOC | [LOC EXT]]; clear J12'.
    + subst l12. destruct (local_of_ESome _ _ _ _ LOC); clear LOC.
      split. apply Fwd1. eauto.
      assert (Plt b2 (Mem.nextblock m2)). eapply VAL3. eassumption.
      xomega.
    + exploit MKI_Some12. eassumption. eassumption.
      intros [E12 | [E12 [b3 [d [E' [B' D]]]]]].
      - subst e12. destruct (extern_of_ESome _ _ _ _ E12); clear E12.
        split. apply Fwd1. eapply VAL3. eauto.
        assert (Plt b2 (Mem.nextblock m2)). eapply VAL3. eassumption.
        xomega.
      - subst b2 d1 e'. destruct (extern_of_ESome _ _ _ _ E'); clear E'.
        assert (Plt b1 (Mem.nextblock m1')). eapply Mem.valid_block_inject_1. apply H0.  eapply MemInjNu'. 
        split. apply H1. xomega. }
  assert (VBj23': forall b2 b3 d2 (J23': j23' b2 = Some(b3,d2)),
            Plt b2 (mem_add_nb m1' m2) /\ Mem.valid_block m3' b3).
  { intros. unfold mem_add_nb. destruct mu23_valid as [VAL1 [VAL2 [VAL3 [VAL4 VAL5]]]].
    subst j23'. destruct (joinD_Some _ _ _ _ _ J23') as [LOC | [LOC EXT]]; clear J23'.
    + subst l23. destruct (local_of_ESome _ _ _ _ LOC); clear LOC.
      split. assert (Plt b2 (Mem.nextblock m2)). eapply VAL1. eassumption. xomega.
      apply Fwd3. eapply VAL3. eassumption.
    + exploit MKI_Some23. eassumption. eassumption.
      intros [E23 | [E23 [E' [E12 GT]]]].
      - subst e23. destruct (extern_of_ESome _ _ _ _ E23); clear E23.
        destruct (VAL3 _ _ _ H0).
        split. assert (Plt b2 (Mem.nextblock m2)). apply H1. xomega.
        apply Fwd3; eauto.
      - subst e'. destruct (extern_of_ESome _ _ _ _ E'); clear E'.
        destruct SMvalNu' as [VV1 [VV2 [VV3 [VV4 VV5]]]]. rewrite Pcompare_eq_Gt in GT.
        destruct (VV3 _ _ _ H0). split; trivial.
        unfold Mem.valid_block in H1. clear - GT H1. unfold Plt in H1. unfold Plt.
        apply (Pos.add_lt_mono_r) with (p:=Mem.nextblock m2) in H1.
        rewrite Pos.sub_add in H1; xomega. }

  exploit (interpolation_II_exists j12 j23 j12' m1 m1' m2 L2 B2); trivial.
  { red; intros. eapply VBj12'; eassumption. }
  { apply MiniINC12. }
  intros [m2' [Cont2' [Acc2' NB2']]].

  exists m2', j12', j23'. split; trivial. split; trivial. split; trivial.
  assert (Fwd2: mem_forward m2 m2').
  { split.
    + unfold Mem.valid_block in *.
                  rewrite NB2'.
                  unfold mem_add_nb.
                  xomega.
    + intros ofs per; unfold Mem.perm. rewrite Acc2'; unfold mem_add_acc.
             destruct (valid_block_dec m2 b); try contradiction.
             (*destruct (Mem.perm_dec m2 b ofs Max Writable).*)
             destruct (B2 b); trivial. 
             destruct (L2 b) eqn: loc23.
             - destruct (source j12 m1 b ofs) eqn:sour; trivial; destruct p.
               symmetry in sour. apply source_SomeE in sour.
               destruct sour as [b1 [delta' [ofs1 [invertible [leq [mapj [mperm ofs_add]]]]]]].
               subst ofs; intros H0. eapply MInj12. eassumption.
               inversion invertible; clear invertible. subst b0 z.
               destruct (Fwd1 _ leq) as [VB' Perms1 (*FwdMax1]*)].
               eapply Perms1. assumption.
             -
               destruct (source j12 m1 b ofs) eqn:sour;
                 try solve[destruct (j23 b); intros HH;try destruct p; trivial; inversion HH].
               destruct p. intros P1'.
                 symmetry in sour. apply source_SomeE in sour.
                 destruct sour as [b1 [delta' [ofs1 [invertible [leq [mapj [mperm ofs_add]]]]]]].
                 subst ofs; eapply MInj12; eauto.
                 inversion invertible; clear invertible. subst b0 z.
                 destruct (Fwd1 _ leq) as [VB' Perms1 (*FwdMax1]*)].
                 eapply Perms1. assumption. }
  assert (MinjValid12': meminj_valid j12' (M1,L1) (M2,L2) m1' m2').
  { split; intros.
    { apply Fwd1. apply mu12_valid; eauto. } split; intros.
    { apply Fwd2. apply mu12_valid; eauto. } split; intros.
    { split. eapply VBj12'; eassumption. 
             unfold Mem.valid_block; rewrite NB2'. eapply VBj12'; eassumption. } 
    split; intros.
    { eapply SMvalNu'; eassumption. }
    { destruct mu12_valid as [VV1 [VV2 [VV3 [VV4 VV5]]]].
      destruct (VV5 _ _ H). split; trivial.
      apply Fwd2; trivial. } }
  assert (MinValid23': meminj_valid j23' (M2,L2) (M3,L3) m2' m3').
  { split; intros.
    { apply Fwd2. apply mu23_valid; eauto. } split; intros.
    { apply Fwd3. apply mu23_valid; eauto. } split; intros.
    { unfold Mem.valid_block; rewrite NB2'. eapply VBj23'; eassumption. }
    split; intros.
    { destruct mu23_valid as [VV1 [VV2 [VV3 [VV4 VV5]]]].
      destruct (VV4 _ _ H). split; trivial.
      apply Fwd2; trivial. }
    { eapply SMvalNu'; eassumption. } } 
  assert (UnchSrc12 :Mem.unchanged_on (o_o_reach j12 L2 m1) m2 m2').
       { constructor.
         + apply mem_forward_nextblock; apply Fwd2. 
         + intros b2 ofs k p [Lb2 P] bval; unfold Mem.perm.
           rewrite Acc2'; unfold mem_add_acc.
           rewrite Lb2.
           destruct (valid_block_dec m2 b2); try solve[contradict bval;trivial].
           destruct (B2 b2). split; auto.
           remember (source j12 m1 b2 ofs) as q.
           destruct q; try solve [split; trivial].
           destruct (source_SomeE _ _ _ _ _ Heqq) as [bb [dd [zz [AA [BB [CC [DD EE]]]]]]].
             subst p0 ofs. elim (P _ _ CC). rewrite Z.add_simpl_r; trivial.
         + intros b2 ofs [Lb2 P] mperm.
           rewrite Cont2'; unfold mem_add_cont. 
           rewrite Lb2. specialize (Mem.perm_valid_block _ _ _ _ _ mperm); intros VB2.
           destruct (valid_block_dec m2 b2); try contradiction.
           (*destruct (Mem.perm_dec m2 b ofs Max Writable); trivial.*)
             (*remember (B b) as d. symmetry in Heqd.
             destruct d; simpl; trivial.
             destruct (RDOnly12 _ Heqd) as [EXTb _].
             assert (LT: locBlocksTgt nu12 b = false). eapply extern_DomRng'; eassumption.
             destruct GlueInv as [GL _]; rewrite GL in LT.
             rewrite LT in locS; discriminate.*)
             destruct (B2 b2); trivial.
             remember (source j12 m1 b2 ofs) as q.
             destruct q; try solve [split; trivial].
             destruct (source_SomeE _ _ _ _ _ Heqq) as [bb [dd [zz [AA [BB [CC [DD EE]]]]]]].
               subst p ofs. elim (P _ _ CC). rewrite Z.add_simpl_r; trivial.
       }
  assert (UnchMid: Mem.unchanged_on (fun b2 z => L2 b2 = true /\ j23 b2 = None) m2 m2').
  { constructor.
         + apply mem_forward_nextblock; apply Fwd2. 
         + intros b2 ofs k p [Lb2 J23] bval; unfold Mem.perm.
           rewrite Acc2'; unfold mem_add_acc.
           rewrite Lb2.
           destruct (valid_block_dec m2 b2); try solve[contradict bval;trivial].
           destruct (B2 b2). split; auto.
           remember (source j12 m1 b2 ofs) as q.
           destruct q; try solve [split; trivial].
           destruct (source_SomeE _ _ _ _ _ Heqq) as [b1 [dd [zz [AA [BB [CC [DD EE]]]]]]].
           subst p0 ofs. destruct UnchSrc as [UnchA UnchB UnchC].
           destruct (UnchB b1 zz k p); trivial.
             - split. rewrite (WDmu12 _ _ _ CC); trivial.
               subst j. unfold compose_meminj; rewrite CC, J23; trivial.
             - split; intros.
               * apply H; clear H H0.
                 exploit Mem.perm_inject_inv. apply MInj12. apply CC. apply H1.
                 intros [X | X]; trivial; contradiction.
               * eapply MInj12. eassumption. apply H0. apply H1.
         + intros b2 ofs [Lb2 J23] mperm.
           rewrite Cont2'; unfold mem_add_cont. 
           rewrite Lb2. specialize (Mem.perm_valid_block _ _ _ _ _ mperm); intros VB2.
           destruct (valid_block_dec m2 b2); try contradiction.
           (*destruct (Mem.perm_dec m2 b ofs Max Writable); trivial.*)
             (*remember (B b) as d. symmetry in Heqd.
             destruct d; simpl; trivial.
             destruct (RDOnly12 _ Heqd) as [EXTb _].
             assert (LT: locBlocksTgt nu12 b = false). eapply extern_DomRng'; eassumption.
             destruct GlueInv as [GL _]; rewrite GL in LT.
             rewrite LT in locS; discriminate.*)
             destruct (B2 b2); trivial.
             remember (source j12 m1 b2 ofs) as q.
             destruct q; try solve [split; trivial].
             destruct (source_SomeE _ _ _ _ _ Heqq) as [b1 [dd [zz [AA [BB [CC [DD EE]]]]]]].
               subst p ofs.
             rewrite J23; trivial. }
  assert (Perm23':forall b2 b3 delta ofs k p, j23' b2 = Some (b3, delta) ->
               Mem.perm m2' b2 ofs k p -> Mem.perm m3' b3 (ofs + delta) k p).
  { intros b2 b3 delta ofs k p J23'.
             unfold Mem.perm. rewrite Acc2'; unfold mem_add_acc.
    destruct (joinD_Some _ _ _ _ _ J23') as [L23 | [L23 E23']]; clear J23'.
    + subst l23. destruct (local_of_ESome _ _ _ _ L23) as [L2true J23].
      rewrite L2true.
      destruct (valid_block_dec m2 b2).
      2: elim n; apply mu12_valid; trivial.
      remember (B2 b2) as q; symmetry in Heqq.
      destruct q. rewrite (HB2 _ Heqq) in L2true; congruence.
      destruct (source j12 m1 b2 ofs) eqn:sour.
      - symmetry in sour.
        destruct (source_SomeE _ _ _ _ _ sour) 
                    as [b1 [d1 [ofs1 [pairs [bval [J12 [mperm ofss]]]]]]].
        subst ofs p0. rewrite <- Zplus_assoc.
        eapply MemInjNu'.
        subst j'. unfold compose_meminj. destruct MiniINC12 as [Inc12a _].
        destruct MiniINC23 as [Inc23a _].
        rewrite (Inc12a _ _ _ J12).
        rewrite (Inc23a _ _ _ J23); trivial.
      - symmetry in sour; intros. eapply UnchTgt.
        * red. rewrite <- (WDmu23 _ _ _ J23). split; trivial. intros.
          subst j. destruct (compose_meminjD_Some _ _ _ _ _ J0) as [bb [dd1 [dd2 [K1 [K2 K3]]]]]; clear J0.
          subst delta0. intros N.
          destruct (eq_block bb b2).
          ++ subst b2; rewrite J23 in K2; inv K2.
             eapply (source_NoneE _ _ _ _ sour b1).
               eapply Mem.valid_block_inject_1. apply K1. apply MInj12.
               eassumption.
               assert (Arith: ofs + dd2 - (dd1 + dd2) = ofs - dd1) by omega.
               rewrite Arith in N; trivial.
          ++ exploit (Mem.mi_no_overlap _ _ _ MInj23 bb b3). apply n. eassumption. eassumption.
             eapply MInj12. eassumption. eassumption.
             eapply Mem.perm_max. eapply Mem.perm_implies. eassumption. constructor.
             intros [X | X]. congruence. omega.
        * eapply MInj23; eauto.
        * eapply MInj23; eauto.
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
        * exploit Mem.perm_inject. apply J23. eassumption. apply H. intros P3.
          assert (B3_b3: B3 b3 = true). 
          { destruct (B2_B3 _ Heqq) as [? [? [? ?]]]. rewrite H0 in J23; inv J23; trivial. }
          admit. (*property of rdonly sets eapply RDOnly_fwd3; trivial.*)
        * remember (source j12 m1 b2 ofs) as r .
          destruct r.
          ++ destruct (source_SomeE _ _ _ _ _ Heqr) 
                    as [b1 [d1 [ofs1 [pairs [bval [J12 [mperm ofss]]]]]]].
             subst ofs p0. rewrite <- Zplus_assoc.
             eapply MemInjNu'.
             subst j'. unfold compose_meminj. destruct MiniINC12 as [Inc12a _].
             destruct MiniINC23 as [Inc23a _].
             rewrite (Inc12a _ _ _ J12).
             rewrite (Inc23a _ _ _ J23); trivial. apply H.
          ++ rewrite J23 in H. simpl in H; contradiction.
      - destruct (valid_block_dec m2 b2).
        * exfalso. clear - v Bb2. rewrite Pcompare_eq_Gt in Bb2. unfold Mem.valid_block in v. xomega.
        * intros.
          remember (source j12' m1' b2 ofs) as r .
          destruct r.
          ++ destruct (source_SomeE _ _ _ _ _ Heqr) 
                    as [b1 [d1 [ofs1 [pairs [bval [J12 [mperm ofss]]]]]]].
             subst ofs p0. rewrite <- Zplus_assoc.
             eapply MemInjNu'. 2: eassumption.
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
                 eapply Fwd1; trivial. eapply Mem.valid_block_inject_1; eauto.
                 eapply Fwd1; trivial. eapply Mem.valid_block_inject_1; eauto.
               - rewrite (WDmu12 _ _ _ H4) in H0. 
                 destruct (ext12' _ _ _ E12_2). congruence.
          + eapply MKI_no_overlap12.
           - apply Heqoutput. 
           - eapply meminj_no_overlap_rcni. eapply MInj12.
             subst e12. apply inject_incr_extern_of. 
           - eapply meminj_no_overlap_rcni. eapply MemInjNu'.
             subst e'. apply inject_incr_extern_of. 
           - trivial.
           - intros. eapply Mem.valid_block_inject_1. 
             eapply inject_incr_extern_of; eassumption. eassumption.
           - intros. eapply Mem.valid_block_inject_2. 
             eapply inject_incr_extern_of; eassumption. eassumption.
           - apply H.
           - eassumption.
           - destruct (ext12' _ _ _ E12_1). destruct MiniINC12 as [Inc12a Inc12b].
             subst j12'. destruct (joinD_Some _ _ _ _ _ H1) as [LL2 | [LL2 EE2]]; clear H1; trivial.
             subst l12. destruct (local_of_ESome _ _ _ _ LL2); clear LL2.
             rewrite (WDmu12 _ _ _ H5) in *; congruence.
           - trivial.
           - trivial. }
         
         (* Prove Mem.inject12'*)
         constructor; trivial.
         + (*Mem.mem_inj j12' m1' m2'*) constructor.
           - { intros b1 b2 delta ofs k p H H0.
               unfold Mem.perm; rewrite Acc2'; 
               unfold mem_add_acc.
               subst j12'; apply joinD_Some in H; 
               destruct H as [L12 | [L12 E12']].
               + subst l12. destruct (local_of_ESome _ _ _ _ L12) as [HL1 J12]; clear L12.
                 destruct (valid_block_dec m2 b2). 
                 2: solve [elim n; eapply Mem.valid_block_inject_2; eauto].
                 rewrite <- (WDmu12 _ _ _ J12), HL1.
                 remember (B2 b2) as Bb2; destruct Bb2; symmetry in HeqBb2.               
                 - specialize (HB2 _ HeqBb2). rewrite <- (WDmu12 _ _ _ J12) in HB2; congruence.
                 - erewrite source_SomeI; try eassumption.
                   * apply MInj12.
                   * apply Fwd1.  eapply Mem.valid_block_inject_1; eauto.
                     eapply Mem.perm_implies. eapply Mem.perm_max; eassumption. constructor.
               + exploit MKI_Some12. eassumption. apply E12'. intros [E12 | [E12 [b3 [d [E' [Hb2 D]]]]]].
                 - subst e12. destruct (extern_of_ESome _ _ _ _ E12) as [HL1 J12]; clear E12.
                   rewrite <- (WDmu12 _ _ _ J12), HL1.
                   destruct (valid_block_dec m2 b2).
                 2: solve [elim n; eapply Mem.valid_block_inject_2; eauto]. 
                   remember (B2 b2) as Bb2. destruct Bb2; symmetry in HeqBb2.
                   * eapply MInj12. eassumption. admit. (*USE RDONLY_fwd1*)
                   * erewrite source_SomeI. eassumption. apply MInj12. eassumption.
                     apply Fwd1.  eapply Mem.valid_block_inject_1; eauto.
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
               red; intros. apply Fwd1. eapply Mem.valid_block_inject_1; eauto. apply H0. eassumption.
             * specialize (MKI_range_eq _ _ _ _ _ _  Heqoutput). intros RNG.
               exploit MKI_Some12. eassumption. apply E12'. intros [E12 | [E12 [b3 [d [E' [GTb2 D]]]]]].
               ++ subst e12. destruct (extern_of_ESome _ _ _ _ E12) as [HL1 J12]; clear E12.
                  eapply MInj12. eassumption.
                  red; intros. apply Fwd1. eapply Mem.valid_block_inject_1; eauto. apply H0. eassumption.
               ++ subst delta. exists 0. trivial.
           - intros b1 ofs b2 delta J12' mperm1'. 
             rewrite Cont2'; unfold mem_add_cont.
             subst j12'. destruct (joinD_Some _ _ _ _ _ J12') as [L12 | [L12 E12']]; clear J12'.
             * subst l12; destruct (local_of_ESome _ _ _ _ L12) as [L1b1 J12].
               rewrite <- (WDmu12 _ _ _ J12), L1b1. 
               destruct (valid_block_dec m2 b2). 2: solve [elim n; eapply Mem.valid_block_inject_2; eauto].
               remember (B2 b2) as Bb2; destruct Bb2; symmetry in HeqBb2.               
               ++ specialize (HB2 _ HeqBb2). rewrite <- (WDmu12 _ _ _ J12) in HB2; congruence.
               ++ erewrite source_SomeI; try eassumption.
                  Focus 2. apply MInj12.
                  Focus 2. apply Fwd1.  eapply Mem.valid_block_inject_1; eauto. eapply Mem.perm_implies. eapply Mem.perm_max. eassumption. constructor.
                  remember (j23 b2) as t. destruct t; symmetry in Heqt. destruct p.
                     ** apply inject_memval_memval_inject1.
                        intros. exploit (Mem.mi_memval _ _ _ (Mem.mi_inj _ _ _ MemInjNu') b1). 
                           eapply ExtIncr. subst j. unfold compose_meminj. rewrite J12, Heqt; reflexivity.
                           eassumption.
                        intros M. subst j'. rewrite H in *. inv M.
                        destruct (val_inject_split _ _ _ _ H1) as [uu [UU1 UU2]]. clear UU2.
                        destruct u; simpl in *; eexists; try reflexivity.
                        inv UU1. rewrite H3. reflexivity.
                     ** destruct UnchSrc as [UA UB UC].
                        assert (SC1: L1 b1 = true /\ j b1 = None).
                        { split; trivial. subst j. unfold compose_meminj. rewrite J12, Heqt; trivial. }
                        assert (SC2: Mem.perm m1 b1 ofs Cur Readable).
                        { apply UB; trivial. eapply Mem.valid_block_inject_1; eauto. }
                        rewrite UC; trivial.
                        eapply memval_inject_incr.
                        -- apply MInj12; eassumption. 
                        -- apply MiniINC12.
             * destruct (ext12' _ _ _ E12') as [L1b1 L2b2]; rewrite L2b2.
               exploit MKI_Some12; try eassumption.
               intros [E12 | [E23 [b3 [d [E' [Hb2 D]]]]]].
               ++ destruct (extern_of_ESome _ _ _ _ E12) as [_ J12].
                  destruct (valid_block_dec m2 b2). 2: elim n; eapply mu12_valid; eauto.
                  remember (B2 b2) as q; symmetry in Heqq.
                  destruct q. admit. (*RDOnly fwd1*)
                  erewrite source_SomeI; try eassumption. 2: apply MInj12.
                  -- apply inject_memval_memval_inject1. intros.
                     destruct (full _ b2 delta L1b1 J12) as [_ [b3 [d2 J23]]].
                     exploit Mem.mi_memval. eapply MemInjNu'. 2: eassumption.
                      eapply ExtIncr. subst j; unfold compose_meminj. rewrite J12, J23; reflexivity.
                     intros MV. subst j'. rewrite H in MV. inv MV.
                        destruct (val_inject_split _ _ _ _ H1) as [uu [UU1 UU2]]. clear UU2.
                        destruct u; simpl in *; eexists; try reflexivity.
                        inv UU1. rewrite H3. reflexivity.
                  -- apply Fwd1. eapply Mem.valid_block_inject_1; eauto. eapply Mem.perm_implies. eapply Mem.perm_max. eassumption. constructor.
               ++ subst delta.
                  destruct (valid_block_dec m2 b2). 
                  -- subst b2; clear - v; unfold Mem.valid_block in v. xomega.
                  -- clear Hb2. destruct (extern_of_ESome _ _ _ _ E') as [_ Jb1]; clear E'.
                     exploit Mem.mi_memval. apply MemInjNu'. eassumption. eassumption.
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
         + intros. unfold Mem.valid_block; rewrite NB2'. eapply VBj12'; eassumption.
         + intros. subst j12'. 
           destruct (joinD_Some _ _ _ _ _ H) as [L12 | [L12 E12']]; clear H.
           - destruct (local_of_ESome _ _ _ _ L12) as [Lb J12]; clear L12.
             eapply MInj12. eassumption. 
             destruct H0.
             left; eapply Fwd1; trivial. eapply Mem.valid_block_inject_1; eauto. 
             right; eapply Fwd1; trivial. eapply Mem.valid_block_inject_1; eauto.
           - exploit MKI_Some12; try eassumption. intros [E12 | [E12 [b3 [d [E' [B' D]]]]]].
             * destruct (extern_of_ESome _ _ _ _ E12).
               eapply MInj12. eassumption. 
               destruct H0.
               left; eapply Fwd1; trivial. eapply Mem.valid_block_inject_1; eauto.
               right; eapply Fwd1; trivial. eapply Mem.valid_block_inject_1; eauto.
             * subst delta. destruct (extern_of_ESome _ _ _ _ E').
               exploit Mem.mi_representable.
               eapply MemInjNu'. eassumption. eassumption. intros [X Y]. 
               destruct (Int.unsigned_range_2 ofs); omega.
         + intros. clear Cont2'. red in FE.
           subst j12'. destruct (joinD_Some _ _ _ _ _ H) as [L12 | [L12 E12']]; clear H.
           - destruct (local_of_ESome _ _ _ _ L12) as [L1b1 J12]. 
             remember (j23 b2) as q; symmetry in Heqq.
             destruct q.
             * destruct p0. apply MiniINC23 in Heqq.
               exploit Perm23'; try eassumption.
               intros. eapply MemInjNu'.
               ++ subst j'. unfold compose_meminj, join. rewrite L12, Heqq; reflexivity.
               ++ rewrite Zplus_assoc; eassumption.
             * assert (Jb1: j b1 = None).
               { subst j; unfold compose_meminj, join. rewrite J12, Heqq; trivial. }
               eapply UnchMid in H0. 
               ++ exploit Mem.mi_perm_inv. apply MInj12. eassumption. apply H0.
                  intros [P | P].
                  -- left; apply UnchSrc; eauto. eapply Mem.valid_block_inject_1; eauto.
                  -- right. intros N. apply P; clear P.
                     apply UnchSrc; eauto. eapply Mem.valid_block_inject_1; eauto.
               ++ rewrite <- (WDmu12 _ _ _ J12). split; trivial.
               ++ eapply Mem.valid_block_inject_2; eauto.
           - exploit MKI_Some12; try eassumption. intros [E12 | [E12 [b [d [E' [GTb2 D]]]]]].
             * destruct (extern_of_ESome _ _ _ _ E12) as [L1b1 J12]. 
               destruct (full' _ _ _ E12') as [b3 [d2 E23']].
               destruct (ext23' _ _ _ E23') as [L2b2 L3b3].
               exploit Perm23'; try eassumption.  
               -- subst j23'. apply joinI. subst l23. rewrite local_of_Ifalse; trivial. right. split; eauto.
               -- intros. eapply MemInjNu'.
                  ** subst j'. unfold compose_meminj, join. rewrite L12, E12'.
                     subst j23' l23; unfold join. rewrite local_of_Ifalse, E23'; eauto.
                  ** rewrite Zplus_assoc; eassumption.
             * subst delta.
               destruct (full' _ _ _ E12') as [b3 [d2 E23']].
               rewrite HE' in E'. unfold compose_meminj in E'. rewrite E12', E23' in E'; inv E'.
               destruct (ext23' _ _ _ E23') as [L2b2 L3b3].
               exploit Perm23'; try eassumption.  
               -- subst j23'. apply joinI. subst l23. rewrite local_of_Ifalse; trivial. right. split; eauto.
               -- intros. eapply MemInjNu'.
                  ** unfold compose_meminj, join. rewrite L12, E12'.
                     subst j23' l23; unfold join. rewrite local_of_Ifalse, E23'; eauto.
                  ** rewrite Zplus_assoc; eassumption. }

    destruct mu23_valid as [V23a [V23b [V23c [V23d V23e]]]].
    destruct mu12_valid as [V12a [V12b [V12c [V12d V12e]]]].

    assert (MInj23': Mem.inject j23' m2' m3').
    { constructor.
      + constructor. assumption.
        - intros b2 b3 delta ch ofs p J23' RP. unfold Z.divide.
          destruct (joinD_Some _ _ _ _ _ J23') as [L23 | [L23 E23']]; clear J23'.
          * destruct (local_of_ESome _ _ _ _ L23).
            eapply MInj23. eassumption.
            red; intros. apply Fwd2. eapply V23c; eassumption. apply RP. apply H1.
          * exploit MKI_Some23; try eassumption. intros [E23 | [E23 [E' [E12 Hb1]]]].
            ++ destruct (extern_of_ESome _ _ _ _ E23).
               eapply MInj23. eassumption.
               red; intros. apply Fwd2. eapply Mem.valid_block_inject_1; eauto. apply RP. apply H1.
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
               eapply MemInjNu'. eassumption.
               instantiate(2:=ofs). instantiate (1:=p). clear -RP Acc2' Hb1 Heqoutput WDmu12 L1b1 ext12' E12' V12c.
               red. intros z Hz.
               unfold Mem.perm in RP. rewrite Acc2' in RP. unfold mem_add_acc in RP.
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
                  ** destruct (extern_of_ESome _ _ _ _ Ebb). elim n; clear n. eapply V12c; eauto.
                  ** subst dd. rewrite Bq, Pos.add_sub, Zplus_0_r. apply RP.
        - { (*mi_memval23*)
            intros b2 ofs b3 delta map23'.
            unfold Mem.perm. rewrite Acc2', Cont2'; clear Acc2' Cont2'. 
            unfold mem_add_cont, mem_add_acc. 
            destruct (joinD_Some _ _ _ _ _ map23') as [Loc23 | [Loc23 Ext23]].
            + destruct (local_of_ESome _ _ _ _ Loc23) as [L2b2 J23b2]; clear Loc23.
              destruct (valid_block_dec m2 b2); [| solve [elim n; eapply V23c; eassumption]].
              rewrite L2b2, J23b2.
              remember (B2 b2) as Bb2; symmetry in HeqBb2.
              destruct Bb2.
              - rewrite (HB2 _ HeqBb2) in *; congruence. 
              - remember (source j12 m1 b2 ofs) as src; destruct src.
                * destruct (source_SomeE _ _ _ _ _ Heqsrc) as [b1 [d1 [zz [HP [Hb1 [J12b1 [PP ZZ]]]]]]].
                  subst p ofs. 
                  intros. rewrite <- Zplus_assoc.
                  exploit Mem.mi_memval. eapply MemInjNu'. 2: apply H. { apply ExtIncr. subst j. unfold compose_meminj. rewrite J12b1, J23b2; reflexivity. }
                  intros MV.
                  inv MV; try constructor.
                  apply val_inject_split in H2. destruct H2 as [u [inj12 inj23]]. simpl.
                  inv inj12; simpl; try constructor; trivial.
                  rewrite H2. econstructor; trivial.
                * destruct UnchTgt as [_ UB UC]; intros P; rewrite UC.
                  ++ eapply memval_inject_incr. apply MInj23. apply J23b2. apply P.
                     apply MiniINC23.
                  ++ red; intros. rewrite <- (WDmu23 _ _ _ J23b2). split; trivial.
                     intros. subst j. destruct (compose_meminjD_Some _ _ _ _ _ J0) as [bb2 [dd1 [dd2 [K1 [K2 DD]]]]]; clear J0.
                     subst delta0. clear UB UC UnchSrc; intros P1.
                     destruct (eq_block bb2 b2).
                     -- subst bb2. rewrite K2 in J23b2. inversion J23b2; subst dd2.
                        eapply source_NoneE. eassumption. 2: apply K1. eapply V12c; eassumption.
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
                destruct (valid_block_dec m2 b2). 2: solve [elim n; eapply V23c; eassumption].
                remember (B2 b2) as Bb2; symmetry in HeqBb2.
                destruct Bb2.
                * admit. (*use RDOnly_fwd3. unfold readonly in RDOnly_fwd3. *) 
                * remember (source j12 m1 b2 ofs) as src.
                  destruct src; [ | contradiction].
                  destruct (source_SomeE _ _ _ _ _ Heqsrc) as [b1 [d1 [zz [HP [Hb1 [J12b1 [PP ZZ]]]]]]].
                     subst p ofs.  
                     intros. rewrite <- Zplus_assoc.
                     exploit Mem.mi_memval. eapply MemInjNu'. 2: apply H. { apply ExtIncr. subst j. unfold compose_meminj. rewrite J12b1, j23b2; reflexivity. }
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
                     exploit Mem.mi_memval. eapply MemInjNu'. 2: apply H. { subst j'. unfold compose_meminj. rewrite J12b1', map23'; reflexivity. }
                     intros MV.
                     inv MV; try constructor.
                     apply val_inject_split in H2. destruct H2 as [u [inj12 inj23]]. simpl.
                     inv inj12; simpl; try constructor; trivial.
                     rewrite H2. econstructor; trivial. }
      + intros b2 VB2. remember (j23' b2) as d; destruct d; trivial; symmetry in Heqd.
        elim VB2; unfold Mem.valid_block. rewrite NB2'. destruct p; eapply VBj23'; eassumption.
      + apply VBj23'.
      + { intros b2 b3 d2 b2' b3' d2' ofs ofs' NEQ j23'b2 j23'b2' Pb2 Pb2'.
          destruct (eq_block b3 b3'). 2: left; assumption. subst b3'.
          destruct (joinD_Some _ _ _ _ _ j23'b2) as [l23_b2 | [l23_b2 e23'_b2]].
          + destruct (local_of_ESome _ _ _ _ l23_b2); clear l23_b2. 
            destruct (joinD_Some _ _ _ _ _ j23'b2') as [l23_b2' | [l23_b2' e23'_b2']].
            - destruct (local_of_ESome _ _ _ _ l23_b2'); clear l23_b2'.
                 eapply MInj23; try eassumption.
                 eapply Fwd2; trivial. eapply V23c; eassumption.
                 eapply Fwd2; trivial. eapply V23c; eassumption.
            - destruct (ext23' _ _ _ e23'_b2').
              rewrite (WDmu23 _ _ _ H0) in *; congruence.
          + destruct (ext23' _ _ _ e23'_b2) as [L2b2 L3b3].
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
                apply Fwd2; trivial. eapply V23c; eassumption.
                apply Fwd2; trivial. eapply V23c; eassumption.
              * destruct (extern_of_ESome _ _ _ _ e23_b2) as [_ j23_b2].
                unfold Mem.perm in Pb2, Pb2'. rewrite Acc2' in *; clear Acc2' Cont2'. unfold mem_add_acc in *.
                destruct (valid_block_dec m2 b2). 2 : solve [ elim n; eapply Mem.valid_block_inject_1; eassumption].
                destruct (valid_block_dec m2 b2'). { clear - v0 GTb1'. unfold Mem.valid_block in v0; xomega. }
                rewrite L2b2 in *.
                remember (source j12' m1' b2' ofs') as src'.
                destruct src'; [ | contradiction].
                destruct (source_SomeE _ _ _ _ _ Heqsrc') as [b1' [d1' [zz' [HP' [Hb1' [j12'b1' [PP' ZZ']]]]]]]; clear Heqsrc'.
                subst p ofs'.
                assert (e12'_b1': e12' b1' = Some (b2', d1')).
                { destruct (joinD_Some _ _ _ _ _ j12'b1') as [LOC | [_ EXT]]; trivial.
                  destruct (local_of_ESome _ _ _ _ LOC) as [L1' J1].
                  rewrite (WDmu12 _ _ _ J1) in L1'. congruence. }
                exploit MKI_Some12. eassumption. apply e12'_b1'. intros [E12' | [E12' [bb3 [dd2' [E' [Bb2' D']]]]]].
                { destruct (extern_of_ESome _ _ _ _ E12') as [? J12'].
                  elim n. eapply V12c; eassumption. }
                subst d1' b2'. rewrite Pos.add_sub in *. rewrite E'b1' in E'. inversion E'; clear E'; subst bb3 dd2'.
                assert (J'b1' : j' b1' = Some (b3, d2')).
                { subst j'. unfold compose_meminj. rewrite j12'b1', j23'b2'; trivial. }
                clear Pb2'. rewrite <- Zplus_assoc; simpl.
                remember (B2 b2) as B2_b2; symmetry in HeqB2_b2; destruct B2_b2.
                { destruct (B2_B3 _ HeqB2_b2) as [bb3 [dd2 [JJ23b2 B3_b3]]].
                  rewrite j23_b2 in JJ23b2. inversion JJ23b2; clear JJ23b2; subst bb3 dd2.
                  admit. (*readonly *) }
                rewrite j23_b2 in Pb2.
                remember (source j12 m1 b2 ofs) as src.
                destruct src; [ | contradiction].
                destruct (source_SomeE _ _ _ _ _ Heqsrc) as [b1 [d1 [zz [HP [Hb1 [j12b1 [PP ZZ]]]]]]]; clear Heqsrc.
                subst p ofs.
                assert (e12_b1: e12 b1 = Some (b2, d1)).
                { rewrite <- (WDmu12 _ _ _ j12b1) in L2b2.
                  subst e12. rewrite extern_of_Ifalse; trivial. }
                clear PP.
                exploit Mem.mi_no_overlap. apply MemInjNu'. 2: eassumption. 3: eassumption. 3: apply Pb2.
                { clear - e12_b1' e12_b1. intros N; subst b1'. congruence. }
                { apply MiniINC12 in j12b1.  
                  subst j'. unfold compose_meminj. rewrite j12b1, j23'b2; reflexivity. }
                rewrite Zplus_assoc. intros [X | X]. elim X; trivial. right; omega. 
              * admit. (*symmetric diagonal case*)
              * destruct (extern_of_ESome _ _ _ _ E'b1) as [L1_b1 J'_b1].
                destruct (extern_of_ESome _ _ _ _ E'b1') as [L1_b1' J'_b1'].
                unfold Mem.perm in Pb2. 
                unfold Mem.perm in Pb2'. rewrite Acc2' in *; clear Acc2' Cont2'.
                unfold mem_add_acc in *.
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
                exploit Mem.mi_no_overlap. apply MemInjNu'. 4: apply Pb2. 4: apply Pb2'.
                ++ intros N; subst b1'. rewrite J12b1' in J12b1''. inversion J12b1''; subst b2' d1'. elim NEQ; trivial.
                ++ subst j'. unfold compose_meminj. rewrite J12b1', j23'b2; reflexivity.
                ++ subst j'. unfold compose_meminj. rewrite J12b1'', j23'b2'; reflexivity.
                ++ intros [X | X]. left; trivial. right. xomega. }
      + intros b2 b3 d2 ofs j23'_b2 P. 
        destruct (joinD_Some _ _ _ _ _ j23'_b2) as [l23_b2 | [l23_b2 e23'_b2]].
        - destruct (local_of_ESome _ _ _ _ l23_b2) as [L2_b2 j23_b2]; clear l23_b2.
          eapply MInj23. eassumption.
          unfold Mem.perm in P. rewrite Acc2' in P; clear Acc2' Cont2'. unfold mem_add_acc in P.
          destruct (valid_block_dec m2 b2). 2: solve[elim n; eapply Mem.valid_block_inject_1; eassumption].
          rewrite L2_b2 in P.
          destruct (B2 b2); trivial. 
          destruct P as [P | P]; [ left | right ].
          * remember (source j12 m1 b2 (Int.unsigned ofs)) as src; destruct src; trivial.
           destruct (source_SomeE _ _ _ _ _ Heqsrc) as [b1 [d1 [zz [HP [Hb1 [J12b1 [PP ZZ]]]]]]].
           subst p; rewrite ZZ. eapply Mem.perm_inject. apply J12b1. apply MInj12. eassumption.
          * remember (source j12 m1 b2 (Int.unsigned ofs-1)) as src; destruct src; trivial.
           destruct (source_SomeE _ _ _ _ _ Heqsrc) as [b1 [d1 [zz [HP [Hb1 [J12b1 [PP ZZ]]]]]]].
           subst p; rewrite ZZ. eapply Mem.perm_inject. apply J12b1. apply MInj12. eassumption.
        - exploit MKI_Some23. eassumption. eassumption. intros [e23_b2 | [e23_b2 [E' [e12_b1 GT1]]]].
          * destruct (extern_of_ESome _ _ _ _ e23_b2) as [L2_b2 j23_b2].
            unfold Mem.perm in P. rewrite Acc2' in P; clear Acc2' Cont2'. unfold mem_add_acc in P.
            destruct (valid_block_dec m2 b2). 2: solve[ elim n; eapply Mem.valid_block_inject_1; eassumption].
            rewrite L2_b2, j23_b2 in P.
            destruct (B2 b2). { eapply MInj23; eassumption. }
            eapply MInj23. eassumption.
            destruct P as [P | P] ; [ left | right ].
            ++ remember (source j12 m1 b2 (Int.unsigned ofs)) as src; destruct src; try contradiction.
               destruct (source_SomeE _ _ _ _ _ Heqsrc) as [b1 [d1 [zz [HP [Hb1 [J12b1 [PP ZZ]]]]]]].
               rewrite ZZ. eapply Mem.perm_inject. apply J12b1. apply MInj12. eassumption.
            ++ remember (source j12 m1 b2 (Int.unsigned ofs-1)) as src; destruct src; try contradiction.
               destruct (source_SomeE _ _ _ _ _ Heqsrc) as [b1 [d1 [zz [HP [Hb1 [J12b1 [PP ZZ]]]]]]].
               rewrite ZZ. eapply Mem.perm_inject. apply J12b1. apply MInj12. eassumption.
          * rewrite Pcompare_eq_Gt in *.
            unfold Mem.perm in P. rewrite Acc2' in *; clear Acc2' Cont2'. unfold mem_add_acc in *.
            destruct (valid_block_dec m2 b2). 
            { clear - v GT1. unfold Mem.valid_block in v; xomega. } rename n into n_b2.
            destruct (extern_of_ESome _ _ _ _ E') as [L1_b1 J'_b1].
            destruct P as [P | P].
            ++ remember (source j12' m1' b2 (Int.unsigned ofs)) as src; destruct src. 2: contradiction.
               destruct (source_SomeE _ _ _ _ _ Heqsrc) as [b1 [d1 [zz [HP [Hb1 [J12b1 [PP ZZ]]]]]]]; subst p.
               subst j12'. destruct (joinD_Some _ _ _ _ _ J12b1) as [l12_b1 | [l12_b1 e12'b1]].
               -- destruct (local_of_ESome _ _ _ _ l12_b1).
                  rewrite (WDmu12 _ _ _ H0) in H.
                  destruct (ext23' _ _ _ e23'_b2) as [EE _]; congruence.
               -- exploit MKI_Some12. eassumption. apply e12'b1. intros [e12b1 | [e12b1 [bb [dd [EE' [Bb2 DD]]]]]].
                  ** destruct (extern_of_ESome _ _ _ _ e12b1). elim n_b2. eapply Mem.valid_block_inject_2; eassumption.
                  ** subst d1. rewrite Zplus_0_r, ZZ in *. 
                     assert (j' b1 = Some (b3, d2)). { subst j'. unfold compose_meminj. rewrite J12b1, j23'_b2; trivial. }
                     exploit Mem.mi_representable. apply MemInjNu'. apply H.
                     left. instantiate (1:=ofs). rewrite ZZ; assumption. rewrite ZZ; trivial.
            ++ remember (source j12' m1' b2 (Int.unsigned ofs-1)) as src; destruct src. 2: contradiction.
               destruct (source_SomeE _ _ _ _ _ Heqsrc) as [b1 [d1 [zz [HP [Hb1 [J12b1 [PP ZZ]]]]]]]; subst p.
               subst j12'. destruct (joinD_Some _ _ _ _ _ J12b1) as [l12_b1 | [l12_b1 e12'b1]].
               -- destruct (local_of_ESome _ _ _ _ l12_b1).
                  rewrite (WDmu12 _ _ _ H0) in H.
                  destruct (ext23' _ _ _ e23'_b2) as [EE _]; congruence.
               -- exploit MKI_Some12. eassumption. apply e12'b1. intros [e12b1 | [e12b1 [bb [dd [EE' [Bb2 DD]]]]]].
                  ** destruct (extern_of_ESome _ _ _ _ e12b1). elim n_b2. eapply Mem.valid_block_inject_2; eassumption.
                  ** subst d1. rewrite Zplus_0_r, ZZ in *. 
                     assert (j' b1 = Some (b3, d2)). { subst j'. unfold compose_meminj. rewrite J12b1, j23'_b2; trivial. }
                     exploit Mem.mi_representable. apply MemInjNu'. apply H.
                     right. instantiate (1:=ofs). rewrite ZZ; assumption. trivial.
      + intros b2 ofs b3 d2 k p j23'_b2 P. 
        destruct (joinD_Some _ _ _ _ _ j23'_b2) as [l23_b2 | [l23_b2 e23'_b2]].
        - destruct (local_of_ESome _ _ _ _ l23_b2) as [L2_b2 j23_b2]; clear l23_b2.
          unfold Mem.perm. rewrite Acc2'; clear Acc2' Cont2'. unfold mem_add_acc.
          destruct (valid_block_dec m2 b2). 2: solve[elim n; eapply Mem.valid_block_inject_1; eassumption].
          rewrite L2_b2.
          remember (B2 b2) as Bb2; symmetry in HeqBb2; destruct Bb2.
          * rewrite (HB2 _ HeqBb2) in *; discriminate.
          * remember (source j12 m1 b2 ofs) as src; destruct src. 
            ++ destruct p0. destruct (source_SomeE _ _ _ _ _ Heqsrc) as [b1 [d1 [zz [HP [Hb1 [J12b1 [PP ZZ]]]]]]].
               inv HP. rewrite <- Zplus_assoc in P.
               eapply MemInjNu'. 2: apply P. eapply MiniINC12 in J12b1. unfold compose_meminj. rewrite J12b1, j23'_b2; trivial.
            ++ assert (vb3: Mem.valid_block m3 b3) by (eapply Mem.valid_block_inject_2; eassumption).
               destruct (Mem.perm_dec m2 b2 ofs Max Nonempty). 2: right; trivial. 
               apply UnchTgt in P; trivial.
               -- eapply MInj23; eassumption.
               -- clear P. red. clear H H0. rewrite <- (WDmu23 _ _ _ j23_b2). split; trivial. clear Perm23' UnchMid UnchSrc12.
                  intros. intros N. subst j. destruct (compose_meminjD_Some _ _ _ _ _ J0) as [bb2 [dd1 [dd2 [K1 [K2 DD]]]]]; clear J0.
                  assert (vb1: Mem.valid_block m1 b1) by (eapply Mem.valid_block_inject_1; eassumption). 
                  destruct (eq_block bb2 b2); subst.
                  ** apply (source_NoneE _ _ _ _ Heqsrc _ _ vb1 K1).
                     rewrite K2 in j23_b2; inv j23_b2.
                     assert (Arith: ofs + d2 - (dd1 + d2) = ofs - dd1) by omega.
                     rewrite Arith in *; trivial.
                  ** clear Heqoutput HE' ExtIncr local_jj' UnchSrc UnchTgt.
                     exploit Mem.perm_inject. apply K1. apply MInj12. apply N. intros P'.
                     exploit Mem.mi_no_overlap. apply MInj23. apply n. eassumption. eassumption. eassumption. eassumption.
                     intros [X | X]. elim X; trivial. omega.
        - destruct (ext23' _ _ _ e23'_b2) as [L2_b2 L3_b3].
          exploit MKI_Some23. eassumption. eassumption. intros [e23_b2 | [e23_b2 [e'_b1 [e12_b1 GT]]]].
          * destruct (extern_of_ESome _ _ _ _ e23_b2) as [_ j23_b2].
            assert (Mem.valid_block m2 b2 /\ Mem.valid_block m3 b3) by (eapply V23c; eassumption).
            destruct H as [vb2 vb3].   
            unfold Mem.perm. rewrite Acc2'; clear Acc2' Cont2'. unfold mem_add_acc.
            destruct (valid_block_dec m2 b2); try contradiction.
            rewrite L2_b2, j23_b2; clear v.
            remember (B2 b2) as Bb2; symmetry in HeqBb2.
            destruct Bb2.
            ++ admit. (*eapply RDOnly_fwd3 in P.  (*property of readonly: B preserved*)
               eapply MInj23. eassumption. eassumption.*)
            ++ remember (source j12 m1 b2 ofs) as src.
               destruct src. 2:solve [right; intros N; apply N].
               destruct (source_SomeE _ _ _ _ _ Heqsrc) as [b1 [d1 [zz [HP [Hb1 [J12b1 [PP ZZ]]]]]]]; subst p0 ofs.
               apply MiniINC12 in J12b1.
               eapply MemInjNu'. 
               -- subst j'. unfold compose_meminj. rewrite J12b1, j23'_b2; reflexivity.
               -- rewrite Zplus_assoc; trivial.
          * destruct (extern_of_ESome _ _ _ _ e'_b1) as [L1_b1 j'_b1]. 
            rewrite Pcompare_eq_Gt in GT.
            unfold Mem.perm. rewrite Acc2'; clear Acc2' Cont2'. unfold mem_add_acc.
            destruct (valid_block_dec m2 b2). { exfalso. clear - v GT. unfold Mem.valid_block in v; xomega. }
            remember (source j12' m1' b2 ofs) as src.
            destruct src. 2:solve [right; intros N; apply N].
            destruct (source_SomeE _ _ _ _ _ Heqsrc) as [b1 [d1 [zz [HP [Hb1 [J12b1 [PP ZZ]]]]]]]; subst p0 ofs.
            eapply MemInjNu'. 
               -- subst j'. unfold compose_meminj. rewrite J12b1, j23'_b2; reflexivity.
               -- rewrite Zplus_assoc; trivial. }

  intuition.
Admitted. (*last condition is RDOnly_fwd m2 m2' B - should be ok*)
 