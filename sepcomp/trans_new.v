Require Import compcert.common.Events.
Require Import compcert.common.Memory.
Require Import compcert.lib.Coqlib.
Require Import compcert.common.Values.
Require Import compcert.lib.Maps.
Require Import compcert.lib.Integers.
Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.
Require Import VST.msl.Axioms.

Require Import VST.sepcomp.mem_lemmas. (*needed for definition of mem_forward etc*)
Require Import VST.sepcomp.semantics.
Require Import VST.sepcomp.semantics_lemmas.
(*Require Import VST.sepcomp.effect_semantics.*)

Require Import VST.sepcomp.structured_injections.
Require Import VST.sepcomp.reach.
Require Export VST.sepcomp.simulations_new.
Require Import VST.sepcomp.simulations_lemmas_new.
(*Require Import VST.sepcomp.effect_properties.*)

Require Import Wellfounded.
Require Import Relations.

Import SM_simulation.

Lemma restrict_cm_compose_sm mu12 mu23:(compose_sm (restrict_sm mu12' (vis mu12'))
           (restrict_sm mu23' (vis mu23'))))) args1 args3 ->
Forall2
  (val_inject
     (as_inj
        (restrict_sm (compose_sm mu12' mu23') (vis (compose_sm mu12' mu23'))

Module TRANSITIVITY. Section TRANS.

Inductive sem_compose_ord_eq_eq {D12 D23:Type}
  (ord12: D12 -> D12 -> Prop) (ord23: D23 -> D23 -> Prop) (C2:Type):
  (D12 * option C2 * D23) ->  (D12 * option C2 * D23) ->  Prop :=
| sem_compose_ord1 :
  forall (d12 d12':D12) (c2:C2) (d23:D23),
    ord12 d12 d12' -> sem_compose_ord_eq_eq ord12 ord23 C2 (d12,Some c2,d23) (d12',Some c2,d23)
| sem_compose_ord2 :
  forall (d12 d12':D12) (c2 c2':C2) (d23 d23':D23),
    ord23 d23 d23' -> sem_compose_ord_eq_eq ord12 ord23 C2 (d12,Some c2,d23) (d12',Some c2',d23').

Lemma well_founded_sem_compose_ord_eq_eq: forall {D12 D23:Type}
  (ord12: D12 -> D12 -> Prop) (ord23: D23 -> D23 -> Prop)  (C2:Type)
  (WF12: well_founded ord12) (WF23: well_founded ord23),
  well_founded (sem_compose_ord_eq_eq ord12 ord23 C2).
Proof.
  intros. intro. destruct a as [[d12 c2] d23].
  revert d12.
  destruct c2.
  2: constructor; intros. 2: inv H.
  revert c.
  induction d23 using (well_founded_induction WF23).
  intros.
  induction d12 using (well_founded_induction WF12).
  constructor; intros. inv H1.
  generalize (H0 d0). simpl. intros.
  apply H1. auto.
  generalize (H d1).
  intros.
  specialize H1. auto.
Qed.

Context
  {F1 V1 C1 F2 V2 C2 F3 V3 C3: Type}
  (Sem1 : @MemSem (Genv.t F1 V1) C1)
  (Sem2 : @MemSem (Genv.t F2 V2) C2)
  (Sem3 : @MemSem (Genv.t F3 V3) C3)
  (ge1 : Genv.t F1 V1)
  (ge2 : Genv.t F2 V2)
  (ge3 : Genv.t F3 V3).

Variable SIM12:SM_simulation_inject Sem1 Sem2 ge1 ge2.
Definition CoreData12:= core_data _ _ _ _ SIM12.
Definition CoreOrd12:= core_ord _ _ _ _ SIM12.
Definition MatchState12:= match_state _ _ _ _ SIM12.
Definition match_sm_wd12:= match_sm_wd _ _ _ _ SIM12.

Variable SIM23:SM_simulation_inject Sem2 Sem3 ge2 ge3.
Definition CoreData23:= core_data _ _ _ _ SIM23.
Definition CoreOrd23:= core_ord _ _ _ _ SIM23.
Definition MatchState23:= match_state _ _ _ _ SIM23.
Definition match_sm_wd23:= match_sm_wd _ _ _ _ SIM23.

Definition coreData:Type  :=
       core_data Sem1 Sem2 ge1 ge2 SIM12 * option C2 *
       core_data Sem2 Sem3 ge2 ge3 SIM23.

Definition CoreOrd:= Relation_Operators.clos_trans _ (sem_compose_ord_eq_eq CoreOrd12 CoreOrd23 C2).

Definition muINV mu12 mu23 := locBlocksTgt mu12 = locBlocksSrc mu23 /\
(*        SM_wd mu12 /\ SM_wd mu23 /\*)
         extBlocksTgt mu12 = extBlocksSrc mu23 /\
        (forall b : block,
         pubBlocksTgt mu12 b = true -> pubBlocksSrc mu23 b = true) /\
        (forall b : block,
         frgnBlocksTgt mu12 b = true -> frgnBlocksSrc mu23 b = true).

Definition MatchState (d:coreData) (mu: SM_Injection) (c1:C1)(m1:mem)(c3:C3)(m3:mem): Prop :=
      match d with (d1,X,d2) =>
        exists c2, exists m2, exists mu1, exists mu2,
          X=Some c2 /\ mu = compose_sm mu1 mu2 /\ muINV mu1 mu2 /\
          MatchState12 d1 mu1 c1 m1 c2 m2 /\ MatchState23 d2 mu2 c2 m2 c3 m3
      end.

Lemma diagram_trans:
forall (d : coreData) (mu : SM_Injection) (c1 : C1) (m1 : mem) 
  (c2 : C3) (m2 : mem) (A1 : MidStepResult),
MatchState d mu c1 m1 c2 m2 ->
midstep Sem1 ge1 c1 m1 A1 ->
exists (A2 : MidStepResult) (cd' : coreData) (mu' : SM_Injection),
  midstep Sem3 ge3 c2 m2 A2 /\
  intern_incr mu mu' /\
  globals_separate ge3 mu mu' /\
  MSR_locally_allocated mu mu' m1 m2 A1 A2 /\
  MSR_relate ge1 ge3 (MatchState cd') mu' A1 A2 /\
  (MSR_unchanged_on (fun (b : block) (_ : Z) => vis mu b = false) m1 A1 ->
   MSR_unchanged_on (extern_out_of_reach mu m1) m2 A2).
Proof. intros. rename c2 into c3. rename m2 into m3. rename H0 into STEP1.
  destruct d as [[d12 X] d23]. simpl in H.
  destruct H as [c2 [m2 [mu12 [mu23 [? [? [INV [MS12 MS23]]]]]]]]; subst.
  destruct (match_midstep _ _ _ _ SIM12 _ _ _ _ _ _ _ MS12 STEP1)
   as [A2 [cd2 [mu12' [STEP2 [INC12 [WD12' [SEP12 [LOCALLOC12 [REL12 UNCH2]]]]]]]]].
  destruct (match_midstep _ _ _ _ SIM23 _ _ _ _ _ _ _ MS23 STEP2)
   as [A3 [cd3 [mu23' [STEP3 [INC23 [WD23' [SEP23 [LOCALLOC23 [REL23 UNCH3]]]]]]]]].
  exists A3. 
  assert (WD12: SM_wd mu12) by (eapply match_sm_wd12; eauto).
  assert (WD23: SM_wd mu23) by (eapply match_sm_wd23; eauto).
  destruct A1; destruct A2; destruct A3; try contradiction.
+ (*midstep_to_atExt*)
  rename c into c1'. rename m into m1'. rename e into f. rename l into args1.
  rename c0 into c2'. rename m0 into m2'. rename e0 into f2. rename l0 into args2.
  rename c4 into c3'. rename m4 into m3'. rename e1 into f3. rename l1 into args3.
  exists (cd2, Some c2', cd3), (compose_sm mu12' mu23'). 
  split; [ solve [trivial] | ].
  split; [ solve [ apply compose_sm_intern_incr; trivial] | ].
  destruct REL12 as [Minj12' [F12 [MRR1 [MRR2 [ARGS12 X12]]]]]; subst f2.
  destruct REL23 as [Minj23' [F23 [_ [MRR3 [ARGS23 X23]]]]]; subst f3.
  simpl.
  split. admit. (*globals_separate*)
  split. { (*INV*)
           clear -  LOCALLOC12 LOCALLOC23.
           destruct mu12; destruct mu12'; destruct mu23; destruct mu23'.
           simpl in *; intuition. }
  split.
  - (*MSR_relate*) 
    split. { (*Mem.inject13'*)  clear X12 X23 UNCH2 UNCH3.
             rewrite compose_sm_as_inj; trivial. 
             + eapply Mem.inject_compose; eassumption.
             + clear -  LOCALLOC12 LOCALLOC23 INV. destruct mu12; destruct mu12'; destruct mu23; destruct mu23'.
               red in INV. simpl in *; intuition; subst; trivial.
             + clear -  LOCALLOC12 LOCALLOC23 INV. destruct mu12; destruct mu12'; destruct mu23; destruct mu23'.
               red in INV. simpl in *; intuition; subst; trivial. }
    split; [ trivial | ].
    split; [ trivial | ].
    split; [ trivial | ].
    split. { (*val_inject arg1 args3*) clear X12 X23 UNCH2 UNCH3. (*
             rewrite <- restrict_sm_all in ARGS12.
             rewrite <- restrict_sm_all in ARGS23.*)
             specialize (forall_val_inject_compose _ _ _ ARGS12 _ _ ARGS23). clear.
             rewrite <- ! restrict_sm_all. rewrite <- compose_sm_as_inj.
unfold restrict_sm; simpl. destruct mu12'; destruct mu23'; simpl.

 intros.

             apply val_list_inject_forall_inject.
             apply forall_inject_val_list_inject in H.
             eapply val_inject_list_incr; [| eassumption].
Print restrict_sm.
            SearchAbout Val.inject_list. Forall2. inject_incr.
Search restrict_sm compose_sm.
  Search as_inj restrict.
             rewrite ! compose_sm_as_inj; trivial. 

Search Forall2 val_inject.
             + rewrite H0, H3, H; trivial. , H4.
             simpl in *. red in LOCALLOC12.  Search intern_incr SM_wd. Search Mem.inject compose_meminj. as_inj compose_sm. red in INC12; simpl in INC12. LOCALLOC12, LOCALLOC23. red in LOCALLOC12.
split.
{ apply (gsep_domain_eq _ _ ge2 ge3); try assumption.

  assert (WD12: SM_wd mu12) by (eapply match_sm_wd12; eauto).
  assert (WD23: SM_wd mu23) by (eapply match_sm_wd23; eauto).
  assert (WD12': SM_wd mu12'). eapply match_sm_wd12; eauto. apply MS12. simpl in REL12.
  assert (WD23': SM_wd mu23') by (eapply match_sm_wd23; eauto).
    assert (pglobals: meminj_preserves_globals g2 (extern_of mu23')).
    eapply match_genv23; eauto.
  assert (INCR: Values.inject_incr (as_inj mu12) (as_inj mu12')) by (eapply intern_incr_as_inj; eauto).
  assert (GLUE: (locBlocksTgt mu12 = locBlocksSrc mu23 /\
           extBlocksTgt mu12 = extBlocksSrc mu23))
    by (destruct INV' as [A [B ?]]; split; assumption).
    assert (gsep12: globals_separate g2 mu12 mu12') by assumption.
    assert (gsep23: globals_separate g2 mu23 mu23').
    { eapply gsep_domain_eq. eauto.
    apply genvs_domain_eq_sym; assumption. }
    intros  b1 b3 d3 map13 map13'.

  destruct (compose_sm_as_injD _ _ _ _ _ map13' WD12' WD23') as [b2 [d1 [d2 [map12 [map23 extra]]]]].
  destruct (compose_sm_as_injD_None _ _ _ WD12 WD23 GLUE map13) as [map12'| [b2' [d [map12' map23']]]].

  - assert (isGlobalBlock g2 b2 = false).
    eapply gsep12; eauto.
    destruct (isGlobalBlock g2 b3) eqn:isglob; [ | reflexivity].
    apply (meminj_preserves_globals_isGlobalBlock _ _ pglobals) in isglob.
    apply WD23' in isglob. destruct isglob as [extS extT].
    rewrite <- (as_inj_extBlocks _ _ _ _ WD23' map23) in extT.
    rewrite <- (intern_incr_extBlocksSrc _ _ InjIncr23) in extT.
    destruct GLUE as [GLUEloc GLUEext].
    rewrite <- GLUEext in extT.
    apply as_injD_None in map12'. destruct map12' as [extmap12 locmap12].
    rewrite (intern_incr_extern _ _ InjIncr12) in extmap12.
    rewrite (intern_incr_extBlocksTgt _ _ InjIncr12) in extT.
    unfold as_inj, join in map12. rewrite extmap12 in map12.
    apply WD12' in map12.
    destruct map12 as [locS locT].
    destruct WD12' as [disj_src disj_tgt _].
    destruct (disj_tgt b2) as [theFalse | theFalse];
    rewrite theFalse in * ; discriminate.
  - assert (HH:as_inj mu12' b1 = Some (b2', d))
      by (eapply INCR; auto).
    rewrite HH in map12; inversion map12; subst.
    eapply gsep23; eauto. }

 Search globals_separate. intern_incr. admit.
  split. admit.
  split. admit.
  split. admit.
  intros. clear - REL12 REL23 UNCH2 UNCH3 H.
  unfold extern_out_of_reach; simpl.
  destruct A3; simpl in *; trivial.
  - destruct A2; try contradiction. destruct A1; try contradiction.
    simpl in *. clear REL12 REL23.
    exploit UNCH2; clear UNCH2.
    * eapply mem_unchanged_on_sub; [ eassumption | intros; simpl ].
      unfold vis in *; simpl in *; trivial.
    * intros. exploit UNCH3; clear UNCH3.
      ++ eapply mem_unchanged_on_sub; [ eassumption | intros; simpl ].
         unfold vis in *; simpl in *. red; intros. ; trivial.
         red; intros.

Lemma Transitivity: SM_simulation_inject Sem1 Sem3 ge1 ge3.
Proof. (*
specialize (match_midstep _ _ _ _ SIM12); intros Diag12.
specialize (match_midstep _ _ _ _ SIM23); intros Diag23.*)
eapply (Build_SM_simulation_inject Sem1 Sem3 ge1 ge3 coreData MatchState).
+ eapply well_founded_sem_compose_ord_eq_eq.
  apply (core_ord_wf Sem1 Sem2 ge1 ge2 SIM12).
  apply (core_ord_wf Sem2 Sem3 ge2 ge3 SIM23).
+ admit.
+ admit.
+ admit.
+ admit.
+ admit.
+ admit.
+ (*corediagram*) intros. rename c2 into c3. rename m2 into m3.
  destruct d as [[d12 X] d23]. simpl in H.
  destruct H as [c2 [m2 [mu12 [mu23 [? [? [MS12 MS23]]]]]]]; subst.
  destruct (match_midstep _ _ _ _ SIM12 _ _ _ _ _ _ _ MS12 H0)
   as [A2 [cd2 [mu12' [STEP2 [INC12 [SEP12 [LOCALLOC12 [REL12 UNCH2]]]]]]]].
  simpl in *.
  destruct (match_midstep _ _ _ _ SIM23 _ _ _ _ _ _ _ MS23 STEP2)
   as [A3 [cd3 [mu23' [STEP3 [INC23 [SEP23 [LOCALLOC23 [REL23 UNCH3]]]]]]]].
  exists A3, (cd2, Some c2, cd3), (compose_sm mu12' mu23'). split; trivial.
  split. admit.
  split. admit.
  split. admit.
  split. admit.
  intros. clear - REL12 REL23 UNCH2 UNCH3 H.
  unfold extern_out_of_reach; simpl.
  destruct A3; simpl in *; trivial.
  - destruct A2; try contradiction. destruct A1; try contradiction.
    simpl in *. clear REL12 REL23.
    exploit UNCH2; clear UNCH2.
    * eapply mem_unchanged_on_sub; [ eassumption | intros; simpl ].
      unfold vis in *; simpl in *; trivial.
    * intros. exploit UNCH3; clear UNCH3.
      ++ eapply mem_unchanged_on_sub; [ eassumption | intros; simpl ].
         unfold vis in *; simpl in *. red; intros. ; trivial.
         red; intros.
Search Mem.unchanged_on.

  - admit. - admit.
  - admit. (* destruct A1; destruct A2; destruct A3; simpl in *; try contradiction.
    * rename c into c1'. rename m into m1'. rename m0 into m2'. 
      rename c4 into c3'. rename m4 into m3'. 
      red in LOCALLOC12. red in LOCALLOC23.
      destruct mu12; destruct mu12'; simpl in *.
      destruct REL12 as [INJ12' [E12 [MRR1 [MRR2 [VINJ12 X12]]]]].
      destruct REL23 as [INJ23' [E23 [MRR2' [MRR3 [VINJ23 X23]]]]]. red.*)
  - admit. (* clear - REL12 REL23. destruct A1; destruct A2; destruct A3; simpl in *; try contradiction.
    * rename c into c1'. rename m into m1'. rename m0 into m2'. 
      rename c4 into c3'. rename m4 into m3'. *)
  - clear - UNCH3 H H1.

econstructor.


Definition WP_trans:
        Wholeprog_sim.Wholeprog_sim Sem1 Sem3 g1 g3 Main GeInv13 (InitInv13 g2) (HaltInv13 g2).

