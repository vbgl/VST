Require Import compcert.lib.Coqlib.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import compcert.common.Events.
Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.

Require Import VST.coarse_sepcomp.coarse_defs.
Require Import VST.coarse_sepcomp.coarse_semantics.
Require Import VST.coarse_sepcomp.coarse_sim.

Require Import VST.coarse_sepcomp.coarse_base.
Require Import VST.coarse_sepcomp.interpolation_EI.
Require Import VST.coarse_sepcomp.interpolation_II.

Lemma inject_split: forall j m1 m3 (Inj:Mem.inject j m1 m3)
  (J: forall b1 b2 d, j b1 = Some(b2,d) -> Mem.valid_block m1 b1 /\ Mem.valid_block m3 b2),
  exists m2 j1 j2, j = compose_meminj j1 j2 /\ full_ext (fun _ : block => false) j1 j2 /\
       Mem.inject j1 m1 m2 /\ Mem.inject j2 m2 m3 /\
  (forall b2 b3 d (J2: j2 b2 = Some (b3, d)), j1 (b2 - 1)%positive = Some (b2, 0) /\ j (b2 - 1)%positive = Some (b3, d)).
Proof. intros.
destruct (interp_II_mem_only Mem.empty Mem.empty Mem.empty m1 m3
  (Mem.flat_inj 1%positive) (Mem.flat_inj 1%positive) j (fun b => false) (fun b=>false) (fun b=>false)
  (fun b => false) (fun b=>false) (fun b=>false))
as [j1 [j2 [m2 X]]]; trivial; try solve [congruence].
+ red; intros. apply compose_meminjD_Some in H. destruct H as [b2 [d1 [d2 [H _]]]].
  apply flatinj_E in H. destruct H as [_ [_ ?]]; xomega.
+ red; intros. apply flatinj_E in H. destruct H as [_ [_ ?]]; xomega.
+ red; intros. unfold Mem.valid_block. simpl. split; [intros N; xomega | trivial].
+ intros. apply flatinj_E in H. destruct H as [_ [_ ?]]; xomega. 
+ intros. apply flatinj_E in H. destruct H as [_ [_ ?]]; xomega. 
+ apply empty_inj. 
+ apply empty_inj.
+ apply empty_fwd.
+ apply empty_fwd.
+ apply unchanged_on_empty. 
+ apply unchanged_on_empty. 
+ exists m2, j1, j2. intuition.
- destruct (H14 _ _ _ J2). apply flatinj_E in H13. destruct H13 as [_ [_ ?]]; xomega. simpl in H13.
  simpl in H13. apply H13.
- destruct (H14 _ _ _ J2). apply flatinj_E in H13. destruct H13 as [_ [_ ?]]; xomega. simpl in H13.
  simpl in H13. apply H13.
Qed.


Module SimulationTransExtInj. Section EXT_INJ.
Context
  {F1 V1 C1 F2 V2 C2 F3 V3 C3: Type}
  (Sem1 : @MemSem (Genv.t F1 V1) C1)
  (Sem2 : @MemSem (Genv.t F2 V2) C2)
  (Sem3 : @MemSem (Genv.t F3 V3) C3)
  (ge1 : Genv.t F1 V1)
  (ge2 : Genv.t F2 V2)
  (ge3 : Genv.t F3 V3)
  (SIM12: SM_simulationEXT.SM_simulation_extend Sem1 Sem2 ge1 ge2)
  (SIM23: SM_simulationINJ.SM_simulation_inject Sem2 Sem3 ge2 ge3).

Theorem ext_inj_trans: SM_simulationINJ.SM_simulation_inject Sem1 Sem3 ge1 ge3.
Proof.
  destruct SIM12
    as [match12 ext12 ext_match12 idle12 resume12 match_extends12 Lvalid12
       globals12 Valid12 initial12 cstep12].
  destruct SIM23
    as [match23 ext23 ext_match23 idle23 resume23 match_inject23 LSvalid23
        LTvalid23 local23 globals23 Valid23 initial23 cstep23].
  eapply SM_simulationINJ.Build_SM_simulation_inject with 
    (match_state := fun j X c1 m1 c3 m3 => match X with (LS,LT) =>
        exists c2 m2,
          match12 LS c1 m1 c2 m2 /\ match23 j (LS,LT) c2 m2 c3 m3
      end)
    (match_ext := fun A1 A3 tp j X c1 args1 m1 c3 args3 m3 => match X with (LS,LT) =>
        exists A2 c2 args2 m2,
          ext12 A1 A2 tp LS c1 args1 m1 c2 args2 m2 /\ 
          ext23 A2 A3 tp j (LS,LT) c2 args2 m2 c3 args3 m3
      end).
{ (*ext_match*) 
  clear - ext_match12 ext_match23.
  intros Res1 Res3 tp j [LS LT] c1 arg1 m1 c3 args3 m3.
  intros [Res2 [c2 [args2 [m2 [A12 A23]]]]].
  destruct (ext_match12 _ _ _ _ _ _ _ _ _ _ A12) as [M12 Args12]; clear ext_match12 A12.
  destruct (ext_match23 _ _ _ _ _ _ _ _ _ _ _ A23) as [M23 Args23]; clear ext_match23 A23.
  split; [exists c2, m2; split; trivial |].
  eapply forall_lessdef_valinject; eassumption. }
{ (*match_idle*) 
  clear - idle12 idle23 ext_match12 ext_match23 match_extends12 match_inject23  local23 Valid23 globals12 globals23.
  intros Res1 Res3 tp j LS LT c1 arg1 m1 c3 args3 m3.
  intros [Res2 [c2 [args2 [m2 [A12 A23]]]]].
  destruct (ext_match12 _ _ _ _ _ _ _ _ _ _ A12) as [M12 Args12]; clear ext_match12.
  destruct (ext_match23 _ _ _ _ _ _ _ _ _ _ _ A23) as [M23 Arg23]; clear ext_match23.
  specialize (idle12 _ _ _ _ _ _ _ _ _ _ A12).
  specialize (idle23 _ _ _ _ _ _ _ _ _ _ _ _ A23).
  
  intros j' m1' m3' Gsep Inc Esep ValidJ' Inj13' Fwd1 Fwd3 USrc UTgt.

  specialize (match_extends12 _ _ _ _ _ M12). specialize (match_inject23 _ _ _ _ _ _ M23).
  assert (Esp23: esep m2 j j' m3 LT).
  { clear - Esep match_extends12. 
    red; intros. destruct (Esep _ _ _ J J') as [SepA SepB]. split; [ intros N | trivial ].
    apply SepA; clear SepA. eapply Mem.valid_block_extends; eassumption. }

  destruct Fwd1. destruct Fwd3.
    specialize (local23 _ _ _ _ _ _ _ M23). specialize (Valid23 _ _ _ _ _ _ M23).
    destruct (globals12 _ _ _ _ _ M12) as [G1 [G2 [G3 [G4 [G5 G6]]]]]; clear globals12.
    destruct (globals23 _ _ _ _ _ _ _ M23) as [K1 [K2 [K3 [K4 [K5 [K6 K7]]]]]]; clear globals23.

  destruct (interp_EI m1 m2 m1' m3 m3' j j' LS LT (ReadOnlyBlocks ge1) (ReadOnlyBlocks ge2) (ReadOnlyBlocks ge3))
     as [m2' [MExt12' [FWD2 [MInj23' [RDO2 [Unch2A Unch2B]]]]]]; try eassumption.
    + intros. specialize (G4 b). unfold ReadOnlyBlocks in H3. destruct (Genv.find_var_info ge2 b); [ apply (G4 g); trivial | discriminate].
    + intros. specialize (Gsep  _ _ _ H3 H4). remember (ReadOnlyBlocks ge3 b3) as r; destruct r; [symmetry in Heqr | trivial].
      apply ReadOnlyBlocks_global in Heqr; congruence.
    + intros. destruct (K6 _ _ _ H3); auto. 
    + intros. apply G5; trivial.
    + intros. apply ReadOnlyBlocks_global in H3; eauto. 
    + red in K1. assert (Fwd2: forward ge2 m2 m2') by (split; trivial).
      exists Res2, c2, args2, m2'; split.
      apply (idle12 m1' m2'); trivial; split; trivial.
      apply (idle23 j' m2' m3'); trivial; clear idle12 idle23. 
      - intros. destruct (ValidJ' _ _ _ H3). split; trivial. eapply (Mem.valid_block_extends _ _ _ MExt12'); eassumption. 
      - split; trivial.
      - clear - match_extends12 UTgt.
        eapply Mem.unchanged_on_implies. apply UTgt. intros; destruct H.
        split; trivial. red; intros. intros N. eapply (H1 _ _ H2). eapply Mem.perm_extends; eauto. }

{ (*match_resume*)
  clear - resume12 resume23. 
  intros Res1 Res3 tp j [LS LT] c1 arg1 m1 c3 args3 m3.
  intros [Res2 [c2 [args2 [m2 [A12 A23]]]]]; intros.
  destruct (resume12 _ _ _ _ _ _ _ _ _ _ A12 _ _ HasTy1 HasTy1) as [st1' [st22' [RES1 [RES2 M12']]]]; clear resume12. 
     apply Val.lessdef_refl.
  destruct (resume23 _ _ _ _ _ _ _ _ _ _ _ A23 _ _ HasTy1 HasTy2 RValInj) as [st2' [st3' [RES22 [RES3 M23']]]]; clear resume23.
  rewrite RES2 in RES22; inv RES22.
  exists st1', st3'; split; [trivial | split; [trivial | exists st2', m2 ; split; trivial]]. }

{ (*match_inject*) clear - match_inject23 match_extends12.
  intros j c1 m1 c3 m3 [LS LT].
  intros [c2 [m2 [M12 M23]]]. eapply Mem.extends_inject_compose; eauto. }
{ (*validS*) clear - Lvalid12. 
  intros j c1 m1 c3 m3 LS LT [c2 [m2 [M12 M23]]] b B. eapply Lvalid12; eassumption. }
{ (*validT*) clear - LTvalid23.
  intros j c1 m1 c3 m3 LS LT [c2 [m2 [M12 M23]]] b B. apply (LTvalid23 _ _ _ _ _ _ _ M23 _ B). }
{ (*local*) clear - local23.
  intros j c1 m1 c3 m3 LS LT [c2 [m2 [M12 M23]]] b1 b3 d B.
  eapply local23; eassumption. }
{ (*Gvalid*) clear - globals12 globals23. 
  intros j c1 m1 c3 m3 LS LT [c2 [m2 [M12 M23]]]. 
  specialize (globals12 _ _ _ _ _ M12); destruct globals12 as [G1 [G2 [GP12 [G3 [G4 G5]]]]]. 
  specialize (globals23 _ _ _ _ _ _ _ M23); destruct globals23 as [_ [GV3 [GP23 [D1 [D2 [D3 D4]]]]]].
  split; [ trivial | split; [trivial  | ]].
  split. { red; intros. specialize (GP23 _ _ _ H).  (*injections: do we need both directions of isGlobalBlock ge1 <-> isGlobalBlock ge2 ?*) admit. }
  split; [trivial | split; [trivial | split; [| trivial]]]. 
  intros b1 b3 d J.
    destruct (D3 _ _ _ J). destruct (G4 b1). split; intros; auto.
    intros. apply (G5 _ H). } 
{ (*Jvalid*) clear - Valid12 Valid23.
  intros j c1 m1 c3 m3 [LS LT] [c2 [m2 [M12 M23]]] b b' d B.
  destruct (Valid23 _ _ _ _ _ _ M23 _ _ _ B). destruct (Valid12 _ _ _ _ _ M12 b). split; [ auto | trivial ]. }
{ (*init*) admit. }
{ (*coarsestep*)
  clear - cstep12 cstep23 local23 Valid12 (*match_inject23 ext_match23*)match_extends12 ext_match12.
  intros j c1 m1 c3 m3 LS LT [c2 [m2 [M12 M23]]] R1 Step1.
  assert (LST: forall b1 b2 d, j b1 = Some (b2, d) -> LS b1 = true -> LT b2 = true).
  { intros. rewrite (local23 _ _ _ _ _ _ _ M23 _ _ _ H) in H0; trivial. }
  destruct R1.
  + rename c into c1'; rename m into m1'. destruct p as [[f vals1] after1].
    destruct (cstep12 _ _ _ _ _ M12 _ Step1) as
       [c2' [m2' [vals2 [after2 [Step2 [Conf12 MAfter12]]]]]]; clear cstep12.
    destruct (cstep23 _ _ _ _ _ _ _ M23 _ Step2) as
       [j' [Inc23 [Isep23 [Gsep23 [c3' [m3' [vals3 [after3 [Step3 [Conf23 MAfter23]]]]]]]]]]; clear cstep23.
   assert (Isep13:isep m1 j j' m3 LT).
   { red; intros. destruct (Isep23 _ _ _ J J') as [SepA SepB]. split; [ intros | trivial ].
    intros N; apply SepA. apply (Valid12 _ _ _ _ _ M12); trivial. }
   exists j'; split; [ trivial | split; [ trivial | split; [ trivial | ]]].
   exists c3', m3', vals3, after3; split; [ trivial | split]. 
   - eapply confinedExt_write_confined; eassumption.
   - exists after2, c2', vals2, m2'; simpl in *.
     rewrite <- (freshblockB_1 m1 m2 _ (Valid12 _ _ _ _ _ M12)) in MAfter23.
     destruct (ext_match12 _ _ _ _ _ _ _ _ _ _ MAfter12) as [M12' _].
     rewrite <- (freshblockB_2 m1' m2' _ (Valid12 _ _ _ _ _ M12')) in MAfter23. split; trivial. 
  + rename c into c1'. rename m into m1'. rename v into v1.
    destruct (cstep12 _ _ _ _ _ M12 _ Step1) as [c2' [m2' [v2 [Step2 [MExt12' [Conf12 Vals12]]]]]]; clear cstep12.
    destruct (cstep23 _ _ _ _ _ _ _ M23 _ Step2) as [j' [Inc2 [Isep2 [Gsep2 [c3' [m3' [v3 [Step3 [Minj23' [Conf23 Vinj23]]]]]]]]]]; clear cstep23.
    assert (ISep13: isep m1 j j' m3 LT).
    { red; intros. destruct (Isep2 _ _ _ J J') as [SepA SepB]. split; [ intros | trivial ].
      apply match_extends12 in M12. intros N; apply SepA. eapply (Mem.valid_block_extends _ _ _ M12); eassumption. }
    exists j'; split; [trivial | split; [ trivial | split; [trivial |]]].
    exists c3', m3', v3; split; [trivial | split; [ trivial | split]]. 
    eapply Mem.extends_inject_compose; eauto.
    eapply confinedExt_write_confined; eassumption.
    eapply lessdef_valinject; eauto.
  + rename m into m1'.
    destruct (cstep12 _ _ _ _ _ M12 _ Step1) as [mi2 [Step2 Conf12]]; clear cstep12.
    destruct (cstep23 _ _ _ _ _ _ _ M23 _ Step2) as [mi3 [Step3 Conf23]]; clear cstep23; simpl in *.
    exists mi3; split; [trivial | intros]. eapply confinedExt_write_confined; eauto.
Admitted. (*ok, apart from globalenv + init*)
End EXT_INJ. End SimulationTransExtInj.

Module SimulationTransEqInj. Section EQ_INJ.
Context
  {F1 V1 C1 F2 V2 C2 F3 V3 C3: Type}
  (Sem1 : @MemSem (Genv.t F1 V1) C1)
  (Sem2 : @MemSem (Genv.t F2 V2) C2)
  (Sem3 : @MemSem (Genv.t F3 V3) C3)
  (ge1 : Genv.t F1 V1)
  (ge2 : Genv.t F2 V2)
  (ge3 : Genv.t F3 V3)
  (SIM12: SM_simulationEQ.SM_simulation_equality Sem1 Sem2 ge1 ge2)
  (SIM23: SM_simulationINJ.SM_simulation_inject Sem2 Sem3 ge2 ge3).

Theorem eq_inj_trans: SM_simulationINJ.SM_simulation_inject Sem1 Sem3 ge1 ge3.
Proof.
  destruct SIM12
    as [match12 ext12 ext_match12 idle12 resume12 Lvalid12  globals12
        eq_global12 eq_readonly12 initial12 cstep12].
  destruct SIM23
    as [match23 ext23 ext_match23 idle23 resume23 match_inject23 LSvalid23
        LTvalid23 local23 globals23 Valid23 initial23 cstep23].
  eapply SM_simulationINJ.Build_SM_simulation_inject with 
    (match_state := fun j X c1 m1 c3 m3 => match X with (LS,LT) =>
        exists c2, match12 LS c1 m1 c2 /\
          match23 j (LS,LT) c2 m1 c3 m3 
      end)
    (match_ext := fun A1 A3 tp j X c1 args1 m1 c3 args3 m3 => match X with (LS,LT) =>
        exists A2 c2,
          ext12 A1 A2 tp LS c1 args1 m1 c2 /\
          ext23 A2 A3 tp j (LS, LT) c2 args1 m1 c3 args3 m3
      end).
{ (*ext_match*) 
  clear - ext_match12 ext_match23.
  intros Res1 Res3 tp j [LS LT] c1 arg1 m1 c3 args3 m3.
  intros [Res2 [c2 [A12 A23]]].
  apply ext_match12 in A12.
  destruct (ext_match23 _ _ _ _ _ _ _ _ _ _ _ A23) as [M23 Args23]; clear ext_match23 A23.
  split; [exists c2; split; trivial | trivial]. }
{ (*match_idle*) 
  clear - idle12 idle23 eq_readonly12.
  intros Res1 Res3 tp j LS LT c1 arg1 m1 c3 args3 m3.
  intros [Res2 [c2 [A12 A23]]].
  specialize (idle12 _ _ _ _ _ _ _ _ A12).
  specialize (idle23 _ _ _ _ _ _ _ _ _ _ _ _ A23).
  intros j' m1' m3' Gsep Inc Esep ValidJ' Inj13' Fwd1 Fwd3 USrc UTgt.

  assert (Fwd2: forward ge2 m1 m1').
  { destruct Fwd1.  split; trivial. eapply RDOnly_contravar. eassumption.
    intros. eapply eq_readonly12; trivial. (*only uses read1 -> read2 of EQ*) }

  exists Res2, c2; split; eauto. }

{ (*match_resume*)
  clear - resume12 resume23. 
  intros Res1 Res3 tp j [LS LT] c1 arg1 m1 c3 args3 m3.
  intros [Res2 [c2 [A12 A23]]]; intros.
  destruct(resume12 _ _ _ _ _ _ _ _ A12 _ HasTy1) as [st1' [st22' [RES1 [RES2 M12']]]]; clear resume12. 
  destruct (resume23 _ _ _ _ _ _ _ _ _ _ _ A23 _ _ HasTy1 HasTy2 RValInj) as [st2' [st3' [RES22 [RES3 M23']]]]; clear resume23.
  rewrite RES2 in RES22; inv RES22.
  exists st1', st3'; split; [trivial | split; [trivial | exists st2'; split; trivial]]. }

{ (*match_inject*) clear - match_inject23.
  intros j c1 m1 c3 m3 [LS LT].
  intros [c2 [M12 M23]]; eapply match_inject23; eassumption. }
{ (*validS*) clear - LSvalid23.
  intros j c1 m1 c3 m3 LS LT [c2 [M12 M23]] b B. eapply LSvalid23; eassumption. }
{ (*validT*) clear - LTvalid23.
  intros j c1 m1 c3 m3 LS LT [c2 [M12 M23]] b B. eapply LTvalid23; eassumption. }
{ (*local*) clear - local23.
  intros j c1 m1 c3 m3 LS LT [c2 [M12 M23]] b1 b3 d B.
  eapply local23; eassumption. }
{ (*Gvalid*) clear - globals12 globals23 eq_global12 eq_readonly12. 
  intros j c1 m1 c3 m3 LS LT [c2 [M12 M23]]. 
  specialize (globals12 _ _ _ _ M12); destruct globals12 as [G1 [G2 [GP12 [G3 G4]]]]. 
  specialize (globals23 _ _ _ _ _ _ _ M23); destruct globals23 as [_ [GV3 [GP23 [D1 [D2 [D3 D4]]]]]].
  assert (GP13: globals_preserved ge1 ge3 j).
  { red; intros. rewrite <- (GP23 _ _ _ H), eq_global12; trivial. }
  split; [ trivial | split; [trivial  | ]].
  split. trivial.
  split; [trivial | split; [trivial | split; [| trivial]]]. 
  intros b1 b3 d J.
    destruct (D3 _ _ _ J). destruct (eq_readonly12 b1). split; intros; auto. }
{ (*Jvalid*) clear - Valid23.
  intros j c1 m1 c3 m3 [LS LT] [c2 [M12 M23]] b b' d B.
  apply (Valid23 _ _ _ _ _ _ M23 _ _ _ B). }
{ (*init*) admit. }
{ (*coarsestep*)
  clear -cstep12 cstep23.
  intros j c1 m1 c3 m3 LS LT [c2 [M12 M23]] R1 Step1.
  destruct R1.
  + rename c into c1'; rename m into m1'. destruct p as [[f vals1] after1].
    destruct (cstep12 _ _ _ _  M12 _ Step1) as
       [c2' [after2 [Step2 MAfter12]]]; clear cstep12.
    destruct (cstep23 _ _ _ _ _ _ _ M23 _ Step2) as
       [j' [Inc23 [Isep23 [Gsep23 [c3' [m3' [vals3 [after3 [Step3 [Conf23 MAfter23]]]]]]]]]]; clear cstep23.
   exists j'; split; [ trivial | split; [ trivial | split; [ trivial | ]]].
   exists c3', m3', vals3, after3; split; [ trivial | split; [ trivial | ]].
   exists after2, c2'; simpl in *. split; trivial.
  + rename c into c1'. rename m into m1'. rename v into v1.
    destruct (cstep12 _ _ _ _ M12 _ Step1) as [c2' Step2]; clear cstep12.
    destruct (cstep23 _ _ _ _ _ _ _ M23 _ Step2) as [j' [Inc2 [Isep2 [Gsep2 [c3' [m3' [v3 [Step3 [Minj23' [Conf32 Vinj12]]]]]]]]]]; clear cstep23.
    exists j'; split; [trivial | split; [ trivial | split; [trivial |]]].
    exists c3', m3', v3. intuition. 
  + rename m into m1'.
    specialize (cstep12 _ _ _ _ M12 _ Step1); simpl in *.
    destruct (cstep23 _ _ _ _ _ _ _ M23 _ cstep12) as [mi3 [Step3 Conf23]]; clear cstep23.
    exists mi3; split; trivial.
Admitted. (*OK, modulo initcore *)
End EQ_INJ. End SimulationTransEqInj.

Module SimulationTransInjInj. Section INJ_INJ.

Lemma interpolation_idle {F1 V1 F2 V2 F3 V3 : Type} 
       (ge1 : Genv.t F1 V1) (ge2 : Genv.t F2 V2) (ge3 : Genv.t F3 V3)
      (j1 j2 j':meminj) 
      (m1 m2 m3 m1' m3': mem) 
      (LS LM LT: Blockset)
      (FE : full_ext LS j1 j2)
      (j1_LS_LM: forall b1 b2 d, j1 b1 = Some (b2, d) -> LS b1 = LM b2)
      (j2_LM_LT: forall b2 b3 d, j2 b2 = Some (b3, d) -> LM b2 = LT b3)

      (INC : inject_incr (compose_meminj j1 j2) j')
      (ESep: esep m1 (compose_meminj j1 j2) j' m3 LT)

      (LSvalid : forall b, LS b = true -> Mem.valid_block m1 b)
      (LMvalid : forall b, LM b = true -> Mem.valid_block m2 b)
      (LTvalid : forall b, LT b = true -> Mem.valid_block m3 b)
      (J1_valid: forall b1 b2 d, j1 b1 = Some (b2, d) -> Mem.valid_block m1 b1 /\ Mem.valid_block m2 b2)
      (j2_valid: forall b2 b3 d, j2 b2 = Some (b3, d) -> Mem.valid_block m2 b2 /\ Mem.valid_block m3 b3)

      (Minj12 : Mem.inject j1 m1 m2) 
      (Minj23 : Mem.inject j2 m2 m3)
      (Minj13': Mem.inject j' m1' m3')
      (Fwd1 : forward ge1 m1 m1')
      (Fwd3 : forward ge3 m3 m3')
      (Jvalid': forall b1 b3 d, j' b1 = Some(b3,d) -> Mem.valid_block m1' b1 /\ Mem.valid_block m3' b3)
      (B3sep: forall b1 b3 d, (compose_meminj j1 j2) b1 = None -> j' b1 = Some(b3,d) -> ReadOnlyBlocks ge3 b3 = false)
      (B2_LM: forall b, ReadOnlyBlocks ge2 b = true -> LM b = false)
      (B2valid : forall b, ReadOnlyBlocks ge2 b = true -> Mem.valid_block m2 b /\ forall ofs, ~ Mem.perm m2 b ofs Max Writable)
      (B2_B3: forall b2 b3 d, j2 b2 = Some (b3, d) -> ReadOnlyBlocks ge2 b2 = true -> ReadOnlyBlocks ge3 b3 = true)
      (B2_B1: forall b1 b2 d, j1 b1 = Some (b2, d) -> ReadOnlyBlocks ge2 b2 = true -> ReadOnlyBlocks ge1 b1 = true)
      (Unch1 : Mem.unchanged_on (fun b _ => LS b = true /\ compose_meminj j1 j2 b = None) m1 m1')
      (Unch3 : Mem.unchanged_on (fun b z => LT b = true /\ loc_out_of_reach (compose_meminj j1 j2) m1 b z) m3 m3'):
exists (j1' j2' : meminj) (m2' : mem),
  inject_incr j1 j1' /\ inject_incr j2 j2' /\ esep m1 j1 j1' m2 LM /\ esep m2 j2 j2' m3 LT /\ 
  full_ext LS j1' j2' /\ j' = compose_meminj j1' j2' /\
  Mem.inject j1' m1' m2' /\ Mem.inject j2' m2' m3' /\
  forward ge2 m2 m2' /\
  Mem.unchanged_on
    (fun (b : block) (z : Z) => LM b = true /\ loc_out_of_reach j1 m1 b z) m2 m2' /\
  Mem.unchanged_on (fun (b : block) (_ : Z) => LM b = true /\ j2 b = None) m2 m2' /\ 
  (forall b1 b2 d, j1' b1 = Some (b2, d) -> Mem.valid_block m1' b1 /\ Mem.valid_block m2' b2) /\
  (forall b2 b3 d, j2' b2 = Some (b3, d) -> Mem.valid_block m2' b2 /\ Mem.valid_block m3' b3) /\

     (forall b2 b3 d (J2': j2' b2 = Some (b3, d)),
         j2 b2 = Some (b3, d) \/
         j2 b2 = None /\ j1' (b2 - (Mem.nextblock m2))%positive = Some (b2, 0) /\
                      j' (b2 - (Mem.nextblock m2))%positive = Some (b3, d) /\ 
                     (compose_meminj j1 j2) ((b2 - (Mem.nextblock m2))%positive) = None /\ 
                     (~ Mem.valid_block m2 b2)).
Proof. intros. destruct Fwd1; destruct Fwd3. 
  exploit interp_II_mem_only; try eassumption. intros [j1' [j2' [m2' X]]]; trivial.
  exists j1', j2', m2'. clear - X. intuition. split; trivial.
Qed.

Context
  {F1 V1 C1 F2 V2 C2 F3 V3 C3: Type}
  (Sem1 : @MemSem (Genv.t F1 V1) C1)
  (Sem2 : @MemSem (Genv.t F2 V2) C2)
  (Sem3 : @MemSem (Genv.t F3 V3) C3)
  (ge1 : Genv.t F1 V1)
  (ge2 : Genv.t F2 V2)
  (ge3 : Genv.t F3 V3)
  (SIM12: SM_simulationINJ.SM_simulation_inject Sem1 Sem2 ge1 ge2)
  (SIM23: SM_simulationINJ.SM_simulation_inject Sem2 Sem3 ge2 ge3).

Theorem inj_inj_trans: SM_simulationINJ.SM_simulation_inject Sem1 Sem3 ge1 ge3.
Proof. 
  destruct SIM12
    as [match12 ext12 ext_match12 idle12 resume12 match_inject12 LSvalid12 LTvalid12
        local12 globals12 Jvalid12 initial12 cstep12].
  destruct SIM23
    as [match23 ext23 ext_match23 idle23 resume23 match_inject23 LSvalid23 LTvalid23
        local23 globals23 Jvalid23 initial23 cstep23].
  eapply SM_simulationINJ.Build_SM_simulation_inject with 
    (match_state := fun j X c1 m1 c3 m3 => match X with (LS,LT) =>
        exists c2 m2 j1 j2 LM,
          j = compose_meminj j1 j2 /\ 
          match12 j1 (LS,LM) c1 m1 c2 m2 /\ match23 j2 (LM, LT) c2 m2 c3 m3  /\
          full_ext LS j1 j2
      end)
    (match_ext := fun A1 A3 tp j X c1 args1 m1 c3 args3 m3 => match X with (LS,LT) =>
        exists A2 c2 args2 m2 j1 j2 LM,
          j = compose_meminj j1 j2 /\ 
          ext12 A1 A2 tp j1 (LS, LM) c1 args1 m1 c2 args2 m2 /\ 
          ext23 A2 A3 tp j2 (LM, LT) c2 args2 m2 c3 args3 m3 /\
          full_ext LS j1 j2
      end).
{ (*ext_match*)
  clear - ext_match12 ext_match23.
  intros A1 A3 tp j [LS LT] c1 args1 m1 c3 args3 m3.
  intros [A2 [c2 [args2 [m2 [j1 [j2 [LM [J [E12 [E23 FE]]]]]]]]]]; subst j.
  destruct (ext_match12 _ _ _ _ _ _ _ _ _ _ _ E12) as [M12 ArgsInj12]; clear ext_match12 E12.
  destruct (ext_match23 _ _ _ _ _ _ _ _ _ _ _ E23) as [M23 ArgsInj23]; clear ext_match23 E23.
  split. 
  + exists c2, m2, j1, j2, LM; repeat split; trivial.
  + eapply Forall2_val_inject_compose; eassumption. }

{ (*ext_idle*) 
  clear resume12 initial12 cstep12 resume23 initial23 cstep23.
  intros A1 A3 tp j LS LT c1 args1 m1 c3 args3 m3.
  intros [A2 [c2 [args2 [m2 [j1 [j2 [LM [J [E12 [E23 FE]]]]]]]]]]; subst j.
  specialize (idle12 _ _ _ _ _ _ _ _ _ _ _ _ E12).
  specialize (idle23 _ _ _ _ _ _ _ _ _ _ _ _ E23).
  intros j' m1' m3' Gsep Inc Sep validJ' Minj' Fwd1 Fwd3 USrc UTgt.
  apply ext_match12 in E12; destruct E12 as [M12 Args12].
  apply ext_match23 in E23; destruct E23 as [M23 Args23].
  assert (Interpol: exists j1' j2' m2', inject_incr j1 j1' /\ inject_incr j2 j2' /\ 
          esep m1 j1 j1' m2 LM /\ esep m2 j2 j2' m3 LT /\ 
          full_ext LS j1' j2' /\ j'=compose_meminj j1' j2' /\
          Mem.inject j1' m1' m2' /\ Mem.inject j2' m2' m3' /\ forward ge2 m2 m2' /\
          Mem.unchanged_on (fun (b : block) (z : Z) => LM b = true /\ loc_out_of_reach j1 m1 b z) m2 m2' /\
          Mem.unchanged_on (fun (b : block) (_ : Z) => LM b = true /\ j2 b = None) m2 m2'  /\
  (forall b1 b2 d, j1' b1 = Some (b2, d) -> Mem.valid_block m1' b1 /\ Mem.valid_block m2' b2) /\
  (forall b2 b3 d, j2' b2 = Some (b3, d) -> Mem.valid_block m2' b2 /\ Mem.valid_block m3' b3) /\
     (forall b2 b3 d (J2': j2' b2 = Some (b3, d)),
         j2 b2 = Some (b3, d) \/
         j2 b2 = None /\ j1' (b2 - (Mem.nextblock m2))%positive = Some (b2, 0) /\
                      j' (b2 - (Mem.nextblock m2))%positive = Some (b3, d) /\ 
                     (compose_meminj j1 j2) ((b2 - (Mem.nextblock m2))%positive) = None /\ 
                     (~ Mem.valid_block m2 b2))).
  { clear idle12 idle23.
    specialize (match_inject12 _ _ _ _ _ _ M12). specialize (match_inject23 _ _ _ _ _ _ M23).
    specialize (LSvalid12 _ _ _ _ _ _ _ M12). specialize (LSvalid23 _ _ _ _ _ _ _ M23).
    specialize (LTvalid12 _ _ _ _ _ _ _ M12). specialize (LTvalid23 _ _ _ _ _ _ _ M23).
    specialize (Jvalid12 _ _ _ _ _ _ M12). specialize (Jvalid23 _ _ _ _ _ _ M23).
    specialize (local12 _ _ _ _ _ _ _ M12). specialize (local23 _ _ _ _ _ _ _ M23). 
    destruct (globals12 _ _ _ _ _ _ _ M12) as [? [? [? [? [? [? ?]]]]]]; clear globals12.
    destruct (globals23 _ _ _ _ _ _ _ M23) as [_ [? [? [? [? [? ?]]]]]]; clear globals23.
    clear M12 M23 SIM12 SIM23 Sem1 Sem2 Sem3 ext_match12 match12 ext_match23 match23.
    apply (interpolation_idle ge1 ge2 ge3); try eassumption.
    + clear - Gsep. intros. specialize (Gsep  _ _ _ H H0).
      remember (ReadOnlyBlocks ge3 b3) as t; destruct t; [symmetry in Heqt | trivial].
      apply ReadOnlyBlocks_global in Heqt; congruence.
    + clear - H11; intros. apply ReadOnlyBlocks_global in H; auto. 
    + clear - H8; unfold ReadOnlyBlocks; intros. specialize (H8 b). 
      destruct (Genv.find_var_info ge2 b); try congruence. eapply H8; [ reflexivity | trivial].
    + clear - H10; intros. apply (H10 _ _ _ H); trivial. (*only one implication needed!*)
    + clear - H4; intros. apply (H4 _ _ _ H); trivial. (*only one implication needed*) }
  destruct Interpol as [j1' [j2' [m2' [Inc1 [Inc2 [ESep1 [ESep2 [FE' [J' [MInj12' [MInj23' [Fwd2 [Unch2A [Unch2B [VB12' [VB23' HJ2']]]]]]]]]]]]]]]]; subst j'.
  assert (Gsep1 : globals_separate ge2 j1 j1').
  { clear - ESep1 ESep2 globals23 M23 FE' Inc2 M12 LSvalid12 Gsep. red; intros.
    remember(isGlobalBlock ge2 b2) as t; destruct t; [symmetry in Heqt; exfalso | trivial]. 
    destruct (ESep1 _ _ _ H H0) as [VB1 _].
    destruct (globals23 _ _ _ _ _ _ _ M23) as [G23a [G23b [G23c [G23d [G23e [G23f G23h]]]]]]; clear globals23.
    specialize (G23h _ Heqt). specialize (G23a _ Heqt).
    remember (LS b1) as q; destruct q; symmetry in Heqq. elim (VB1 (LSvalid12 _ _ _ _ _ _ _ M12 _ Heqq)).
    destruct (FE' _ _ _ H0 Heqq) as [b3 [d3 J23']].
    remember (j2 b2) as w; symmetry in Heqw; destruct w; [destruct p | destruct (ESep2 _ _ _ Heqw J23'); contradiction].
    specialize (Inc2 _ _ _ Heqw); rewrite J23' in Inc2; inv Inc2.
    rewrite (G23c _ _ _ Heqw), (Gsep b1 b (d+z)) in Heqt; [ congruence | | ]; unfold compose_meminj.
    rewrite H; trivial. rewrite H0, J23'; trivial. }
  assert (Gsep2 : globals_separate ge3 j2 j2').
  { red; intros b2 b3; intros. 
    remember (isGlobalBlock ge3 b3) as t; destruct t; [ symmetry in Heqt; exfalso | trivial].
    destruct (ESep2 _ _ _ H H0) as [VB2 _].
    destruct (globals23 _ _ _ _ _ _ _ M23) as [G23a [G23b [G23c [_ [_ [_ G23h]]]]]]; clear globals23.
    specialize (G23c b2). specialize (G23b _ Heqt).  
    destruct (HJ2' _ _ _ H0); [ congruence | ]. destruct H1 as [_ [_ [A [B _]]]].
    rewrite (Gsep _ _ _ B A) in Heqt; congruence. }

  assert (U1: Mem.unchanged_on (fun (b : block) (_ : Z) => LS b = true /\ j1 b = None) m1 m1').
  { eapply Mem.unchanged_on_implies. eassumption. simpl; intros b z [LocS J1] Vb.
    split; [ trivial | unfold compose_meminj ]. rewrite J1; trivial. }

  specialize (idle12 _ _ _ Gsep1 Inc1 ESep1 VB12' MInj12' Fwd1 Fwd2 U1 Unch2A).

  assert (U3: Mem.unchanged_on (fun (b : block) (z : Z) => LT b = true /\ loc_out_of_reach j2 m2 b z) m3 m3').
  { eapply Mem.unchanged_on_implies. eassumption. simpl; intros b3 z [Loc3 LOOR23] Vb3.
    split; [ trivial | unfold loc_out_of_reach; intros b1 d J P ].
    apply compose_meminjD_Some in J. destruct J as [b2 [d1 [d2 [J1 [J2 D]]]]]; subst.
    apply match_inject12 in M12.
    eapply (LOOR23 _ _ J2). specialize (Mem.perm_inject _ _ _ _ _ _ _ _ _ J1 M12 P).
    replace (z - (d1 + d2) + d1) with (z-d2); [ trivial | omega]. }

  specialize (idle23 _ _ _ Gsep2 Inc2 ESep2 VB23' MInj23' Fwd2 Fwd3 Unch2B U3).
  exists A2, c2, args2, m2', j1', j2', LM.
  repeat split; trivial. }

{ (*resume*)
  clear - resume12 resume23 ext_match12 ext_match23.
  intros A1 A3 tp j [LS LT] c1 args1 m1 c3 args3 m3.
  intros [A2 [c2 [args2 [m2 [j1 [j2 [LM [J [E12 [E23 FE]]]]]]]]]]; subst j.
  specialize (resume12 _ _ _ _ _ _ _ _ _ _ _ E12).
  specialize (resume23 _ _ _ _ _ _ _ _ _ _ _ E23).
  destruct (ext_match12  _ _ _ _ _ _ _ _ _ _ _ E12) as [Match12 Vinj12]; clear ext_match12.
  destruct (ext_match23  _ _ _ _ _ _ _ _ _ _ _ E23) as [Match23 Vinj23]; clear ext_match23.
  intros ret1 ret3 HT1 HT3 RValInj. apply val_inject_split in RValInj. destruct RValInj as [ret2 [Rinj12 Rinj23]].
  assert (HT2: Val.has_type ret2 tp). 
  { clear - Rinj12 Rinj23 HT1 HT3. destruct ret1; destruct ret2; destruct ret3; inv Rinj12; inv Rinj23; simpl; trivial. }
  
  destruct (resume12 _ _ HT1 HT2 Rinj12) as [st1' [st22' [RET1 [RET2 Match12']]]]; clear resume12.
  destruct (resume23 _ _ HT2 HT3 Rinj23) as [st2' [st3' [RET22 [RET3 Match23']]]]; clear resume23.
  rewrite RET2 in RET22; inv RET22. exists st1', st3'. split; [trivial | split; [trivial | exists st2', m2, j1, j2, LM]]. 
  repeat (split; trivial). }

{ (*match_inject*) clear - match_inject12 match_inject23.
  intros j c1 m1 c3 m3 [LS LT].
  intros [c2 [m2 [j1 [j2 [LM [J [M12 [M23 FE]]]]]]]]; subst.
  eapply Mem.inject_compose; eauto. }
{ (*validS*) clear - LSvalid12.
  intros j c1 m1 c3 m3 LS LT [c2 [m2 [j1 [j2 [LM [J [M12 [M23 FE]]]]]]]] b B. eapply LSvalid12; eassumption. }
{ (*validT*) clear - LTvalid23.
  intros j c1 m1 c3 m3 LS LT [c2 [m2 [j1 [j2 [LM [J [M12 [M23 FE]]]]]]]] b B. eapply LTvalid23; eassumption. }
{ (*local*) clear - local12 local23.
  intros j c1 m1 c3 m3 LS LT [c2 [m2 [j1 [j2 [LM [J [M12 [M23 FE]]]]]]]] b1 b3 d B; subst.
  apply compose_meminjD_Some in B. destruct B as [b2 [d1 [d2 [J1 [J2 D]]]]]; subst.
  erewrite local12; [ | eassumption | eassumption].
  eapply local23; eassumption. }
{ (*Gvalid*) clear - globals12 globals23. 
  intros j c1 m1 c3 m3 LS LT [c2 [m2 [j1 [j2 [LM [J [M12 [M23 FE]]]]]]]]. 
  specialize (globals12 _ _ _ _ _ _ _ M12); destruct globals12 as [G1 [G2 [GP12 [G3 [G4 [G5 G6]]]]]]. 
  specialize (globals23 _ _ _ _ _ _ _ M23); destruct globals23 as [_ [GV3 [GP23 [_ [D1 [D2 D3]]]]]]. 
  split; [ trivial | split; [ trivial | split; [trivial | ]]]. 
  + subst j; intros b1 b3 d J. apply compose_meminjD_Some in J; destruct J as [b2 [d1 [d2 [J1 [J2 D]]]]].
    rewrite (GP12 _ _ _ J1). apply (GP23 _ _ _ J2).
  + split; [ trivial | split; [trivial | split ; [|trivial]]].
    subst j; intros b1 b3 d J. apply compose_meminjD_Some in J; destruct J as [b2 [d1 [d2 [J1 [J2 D]]]]]. 
    destruct (G5 _ _ _ J1). destruct (D2 _ _ _ J2). split; intros; auto. }
{ (*Jvalid*)
  clear - Jvalid12 Jvalid23.
  intros j c1 m1 c3 m3 [LS LT] [c2 [m2 [j1 [j2 [LM [J [M12 [M23 FE]]]]]]]] b b' d B; subst.
  apply compose_meminjD_Some in B. destruct B as [b2 [d1 [d2 [J1 [J2 D]]]]]; subst.
  destruct (Jvalid12 _ _ _ _ _ _ M12 _ _ _ J1).
  destruct (Jvalid23 _ _ _ _ _ _ M23 _ _ _ J2).
  split; trivial. }
{ (*init*) 
  clear -initial12 initial23 globals12 globals23.
  intros until j. intros vals3 m3 IC1 MInj13 Vinj13 GV1 GV3 GP13 MRR1 MRR3 JValid.
  destruct (inject_split _ _ _ MInj13 JValid) as [m2 [j1 [j2 [J [FE [MInj12 [MInj23 JJ]]]]]]].
  subst j.
  apply forall_val_inject_split in Vinj13. destruct Vinj13 as [vals2 [Vinj12 Vinj23]].
  assert (GV2: globals_valid ge2 m2).
  { red; intros. admit. }
  assert (GP12: globals_preserved ge1 ge2 j1).
  { red; intros. admit. }
  assert (MRR2: mem_respects_readonly ge2 m2).
  { red; intros. admit. }
  destruct (initial12 _ _ _ _ _ _ _ IC1 MInj12 Vinj12) as [c2 [IC2 MATCH12]]; trivial.
  { intros. destruct (FE b1 _ _ H) as [b3 [d2 J2]]. reflexivity.
    destruct (JJ _ _ _ J2); clear JJ.
    assert (VB1: Mem.valid_block m1 b1).
    - eapply JValid. unfold compose_meminj. rewrite H, J2; trivial. 
    - split; trivial. eapply MInj12; eauto. }
  assert (GP23: globals_preserved ge2 ge3 j2).
  { red; intros. admit. }  
  destruct (initial23 _ _ _ _ _ _ _ IC2 MInj23 Vinj23) as [c3 [IC3 MATCH23]]; trivial.
  { intros. destruct (JJ _ _ _ H); clear JJ.
    assert (VB1: Mem.valid_block m2 b1) by (eapply MInj12; eauto).
    split; [ trivial | eapply MInj23; eauto]. }
  exists c3; split; trivial.
  exists c2, m2, j1, j2, (fun _ : block => false).
  split; trivial. split; trivial. split; trivial. }
{ (*coarsestep*)
  clear initial12 idle12 initial23 idle23.
  intros j c1 m1 c3 m3 LS LT [c2 [m2 [j1 [j2 [LM [J [M12 [M23 FE]]]]]]]] R1 Step1; subst.
  destruct R1.
  + rename c into c1'; rename m into m1'. destruct p as [[f vals1] after1].
    destruct (cstep12 _ _ _ _ _ _ _ M12 _ Step1) as
       [j1' [Inc12 [ISep12 [Gsep12 [c2' [m2' [vals2 [after2 [Step2 [Conf12 MAfter12]]]]]]]]]]; clear cstep12.
    destruct (cstep23 _ _ _ _ _ _ _ M23 _ Step2) as
       [j2' [Inc23 [ISep23 [Gsep23 [c3' [m3' [vals3 [after3 [Step3 [Conf23 MAfter23]]]]]]]]]]; clear cstep23.
    exists (compose_meminj j1' j2').
      split. apply inject_incr_compose_meminj; trivial.
      split. { specialize (Jvalid12 _ _ _ _ _ _ M12). 
               specialize (Jvalid23 _ _ _ _ _ _ M23).
               specialize (local23 _ _ _ _ _ _ _ M23).
               eapply isep_compose; try eassumption. }
   split. { specialize (globals23 _ _ _ _ _ _ _ M23). destruct globals23 as [GV2 [GV3 [GP23 _]]].
             clear - Inc12 Inc23 Gsep12 Gsep23 GP23. 
            eapply globals_separate_compose_meminj ; eassumption. }
    exists c3', m3', vals3, after3.
      split; [trivial |].
      split. { specialize (local23 _ _ _ _ _ _ _ M23); clear - local23 Conf12 Conf23.
               eapply write_confined_compose; eassumption. }
    remember (fun b : block => LS b || freshblockB m1 m1' b) as LS'.
    remember (fun b : block => LM b || freshblockB m2 m2' b) as LM'.
    remember (fun b : block => LT b || freshblockB m3 m3' b) as LT'.
    simpl in *.
    exists after2, c2', vals2, m2', j1', j2', LM'.
    split; trivial. split; trivial. split; trivial. 
    subst. destruct (ext_match12 _ _ _ _ _ _ _ _ _ _ _ MAfter12) as [MM12 _].
           eapply full_ext_compose; try eassumption. eauto.
  + rename c into c1'. rename m into m1'. rename v into v1.
    destruct (cstep12 _ _ _ _ _ _ _ M12 _ Step1) as [j1' [Inc1 [Isep1 [Gsep1 [c2' [m2' [v2 [Step2 [Minj12' [Conf12 Vinj12]]]]]]]]]]; clear cstep12.
    destruct (cstep23 _ _ _ _ _ _ _ M23 _ Step2) as [j2' [Inc2 [Isep2 [Gsep2 [c3' [m3' [v3 [Step3 [Minj23' [Conf23 Vinj23]]]]]]]]]]; clear cstep23.
    exists (compose_meminj j1' j2').
    split. apply inject_incr_compose_meminj; trivial. 
    split. { specialize (Jvalid12 _ _ _ _ _ _ M12).
             specialize (Jvalid23 _ _ _ _ _ _ M23).
             specialize (local23 _ _ _ _ _ _ _ M23).
             eapply isep_compose; eassumption. }
    split. { specialize (globals23 _ _ _ _ _ _ _ M23). destruct globals23 as [GV2 [GV3 [GP23 _]]].
            clear - Inc1 Inc2 Gsep1 Gsep2 GP23. 
            eapply globals_separate_compose_meminj ; eassumption. }
    exists c3', m3', v3.
    split; [ trivial | ]. 
    split. eapply Mem.inject_compose; eassumption. 
    split. { specialize (local23 _ _ _ _ _ _ _ M23); clear - local23 Conf12 Conf23.
             eapply write_confined_compose; eassumption. }
    eapply val_inject_compose; eassumption.
  + rename m into m1'.
    destruct (cstep12 _ _ _ _ _ _ _ M12 _ Step1) as [mi2 [Step2 Conf12]]; clear cstep12.
    destruct (cstep23 _ _ _ _ _ _ _ M23 _ Step2) as [mi3 [Step3 Conf23]]; clear cstep23.
    exists mi3; split; trivial. intros.
          specialize (Jvalid23 _ _ _ _ _ _ M23).
          specialize (local23 _ _ _ _ _ _ _ M23).
          eapply write_confined_compose; eauto. }
Admitted. (*OK, with exception of initcore*)
End INJ_INJ. End SimulationTransInjInj.