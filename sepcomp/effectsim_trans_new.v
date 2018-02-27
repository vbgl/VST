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
Require Import VST.sepcomp.effect_semantics.

Require Import VST.sepcomp.structured_injections.
Require Import VST.sepcomp.reach.
Require Export VST.sepcomp.effect_simulations_new.
Require Import VST.sepcomp.effect_simulations_lemmas_new.
Require Import VST.sepcomp.effect_properties.

Require Import Wellfounded.
Require Import Relations.

Lemma if_true: forall (A: Prop) (E: {A}+{~A}) (T: Type) (B C: T), A -> (if E then B else C) = B.
Proof.
intros.
destruct E; auto.
contradiction.
Qed.

Lemma if_false: forall (A: Prop) (E: {A}+{~A}) (T: Type) (B C: T), ~A -> (if E then B else C) = C.
Proof.
intros.
destruct E; auto.
contradiction.
Qed.

Lemma compose_sm_sharedSrc mu12 mu23: forall
     (HP: forall b, pubBlocksTgt mu12 b = true -> pubBlocksSrc mu23 b = true)
     (HF: forall b, frgnBlocksTgt mu12 b = true -> frgnBlocksSrc mu23 b = true)
     (WD12: SM_wd mu12) (WD23: SM_wd mu23),
  sharedSrc (compose_sm mu12 mu23) = sharedSrc mu12.
Proof. intros. 
  rewrite (sharedSrc_iff_frgnpub mu12); trivial.
  rewrite (sharedSrc_iff_frgnpub (compose_sm mu12 mu23)).
     trivial.
  eapply compose_sm_wd; eassumption.
Qed.
 
Lemma compose_sm_exportedSrc mu12 mu23 vals: forall
     (HP: forall b, pubBlocksTgt mu12 b = true -> pubBlocksSrc mu23 b = true)
     (HF: forall b, frgnBlocksTgt mu12 b = true -> frgnBlocksSrc mu23 b = true)
     (WD12: SM_wd mu12) (WD23: SM_wd mu23),
  exportedSrc (compose_sm mu12 mu23) vals = exportedSrc mu12 vals.
Proof. intros. unfold exportedSrc.  
  rewrite compose_sm_sharedSrc; trivial. 
Qed. 

Lemma compose_sm_sharedTgt mu12 mu23:
  sharedTgt (compose_sm mu12 mu23) = sharedTgt mu23.
Proof. intros. reflexivity. Qed.

Lemma compose_sm_exportedTgt mu12 mu23 vals:
  exportedTgt (compose_sm mu12 mu23) vals = exportedTgt mu23 vals.
Proof. intros. reflexivity. Qed.

Lemma restrict_sm_compose_sm mu12 mu23: SM_wd mu12 ->
locBlocksTgt mu12 = locBlocksSrc mu23 ->
(forall b, frgnBlocksTgt mu12 b = true -> frgnBlocksSrc mu23 b = true) ->
compose_sm (restrict_sm mu12 (vis mu12))
           (restrict_sm mu23 (vis mu23)) = 
restrict_sm (compose_sm mu12 mu23) (vis (compose_sm mu12 mu23)).
Proof. unfold restrict_sm, compose_sm, vis; intros.
 destruct mu12; destruct mu23; simpl in *; subst.
 f_equal.
+ unfold restrict, compose_meminj; simpl.
  extensionality b.
  remember (locBlocksSrc b) as l; symmetry in Heql.  
  destruct l; simpl.
  - remember (local_of b) as k; symmetry in Heqk. 
    destruct k; trivial.
    destruct p as [b' d].
    specialize (local_DomRng _ H _ _ _ Heqk); simpl in *. intros [_ Y].
    rewrite Y. simpl; trivial.
  - specialize (locBlocksSrc_false_local_None _ _ H Heql); simpl; intros Q.
    rewrite Q.
    destruct (frgnBlocksSrc b); trivial.
+ unfold restrict, compose_meminj; simpl.
  extensionality b.
  remember (locBlocksSrc b || frgnBlocksSrc b) as l; symmetry in Heql.
  destruct l; simpl; trivial.
  remember (extern_of b) as k; symmetry in Heqk. 
  destruct k; trivial. destruct p as [b' d].
  destruct (extern_DomRng' _ H b b' d Heqk) as [? [? [L [L' [? [? _]]]]]]; simpl in *.
  rewrite L'; simpl. rewrite L in Heql; simpl in Heql.
  destruct (frgnSrcAx _ H b Heql) as [bb [dd [XX YY]]]; simpl in *.
  rewrite XX in Heqk; inv Heqk.
  apply H1 in YY; rewrite YY; trivial.
Qed.

Definition muINV mu12 mu23 := locBlocksTgt mu12 = locBlocksSrc mu23 /\
         extBlocksTgt mu12 = extBlocksSrc mu23 /\
        (forall b : block,
         pubBlocksTgt mu12 b = true -> pubBlocksSrc mu23 b = true) /\
        (forall b : block,
         frgnBlocksTgt mu12 b = true -> frgnBlocksSrc mu23 b = true).

Lemma compose_sm_confined (W1 W2 W3: block -> Z -> Prop)
      (mu12 mu23 : SM_Injection)
      (INV : muINV mu12 mu23)
      (CONF12 : confined W1 W2 mu12)
      (CONF23 : confined W2 W3 mu23)
      (WD12 : SM_wd mu12)
      (WD23 : SM_wd mu23):
      confined W1 W3 (compose_sm mu12 mu23).
Proof. red. simpl. 
    intros b3 z EB3 HW3. 
    simpl in CONF23, CONF23. 
    destruct (CONF23 _ _ EB3 HW3) as [b2 [d2 [FRGN2 HW2]]].
    assert (EB2: extBlocksTgt mu12 b2 = true).
    { destruct INV as [INVa [INVb INVc]]; rewrite INVb. 
      eapply foreign_DomRng; eauto. }
    destruct (CONF12 _ _ EB2 HW2) as [b1 [d1 [FRGN1 HW1]]].
    simpl in HW1; rewrite <- Z.sub_add_distr in HW1. 
    exists b1, (d2+d1); split; trivial.
    assert (Fsrc1 :  frgnBlocksSrc mu12 b1 = true).
    { eapply foreign_DomRng; eauto. }
    rewrite Fsrc1, Z.add_comm.
    apply foreign_in_extern in FRGN1. apply foreign_in_extern in FRGN2.
    eapply compose_meminjI_Some; eauto.
Qed.

Import SM_simulation.

Module SM_TRANSITIVITY. Section TRANS.

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
  (Sem1 : @EffectSem (Genv.t F1 V1) C1)
  (Sem2 : @EffectSem (Genv.t F2 V2) C2)
  (Sem3 : @EffectSem (Genv.t F3 V3) C3)
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

Definition MatchState (d:coreData) (mu: SM_Injection) (c1:C1)(m1:mem)(c3:C3)(m3:mem): Prop :=
      match d with (d1,X,d2) =>
        exists c2, exists m2, exists mu1, exists mu2,
          X=Some c2 /\ mu = compose_sm mu1 mu2 /\ muINV mu1 mu2 /\
          MatchState12 d1 mu1 c1 m1 c2 m2 /\ MatchState23 d2 mu2 c2 m2 c3 m3
      end.

Lemma diagram_trans:
forall (d : coreData) (mu : SM_Injection) (c1 : C1) (m1 : mem) 
  (c3 : C3) (m3 : mem) (A1 : MidStepTrackResult),
MatchState d mu c1 m1 c3 m3 ->
midstepT Sem1 ge1 c1 m1 A1 ->
exists (A3 : MidStepTrackResult) (cd' : coreData) (mu' : SM_Injection),
  midstepT Sem3 ge3 c3 m3 A3 /\
  intern_incr mu mu' /\
(*  globals_separate ge3 mu mu' /\*)
  MST_locally_allocated mu mu' m1 m3 A1 A3 /\
  MST_relate ge1 ge3 (MatchState cd') mu' A1 A3 /\
  confined (Wset A1) (Wset A3) mu (*
  (MSR_unchanged_on (fun (b : block) (_ : Z) => vis mu b = false) m1 A1 ->
   MSR_unchanged_on (extern_out_of_reach mu m1) m2 A2)*).
Proof. intros. rename H0 into STEP1.
  destruct d as [[d12 X] d23]. simpl in H.
  destruct H as [c2 [m2 [mu12 [mu23 [? [? [INV [MS12 MS23]]]]]]]]; subst.
  destruct (match_midstep _ _ _ _ SIM12 _ _ _ _ _ _ _ MS12 STEP1)
   as [A2 [cd2 [mu12' [STEP2 [INC12 [LOCALLOC12 [REL12 CONF12]]]]]]]. (* [WD12' [SEP12 [LOCALLOC12 [REL12 UNCH2]]]]]]]]].*)
  destruct (match_midstep _ _ _ _ SIM23 _ _ _ _ _ _ _ MS23 STEP2)
   as [A3 [cd3 [mu23' [STEP3 [INC23 [LOCALLOC23 [REL23 CONF23]]]]]]]. (* [WD23' [SEP23 [LOCALLOC23 [REL23 UNCH3]]]]]]]]].*)
  exists A3. 
  assert (WD12: SM_wd mu12) by (eapply match_sm_wd12; eauto).
  assert (WD23: SM_wd mu23) by (eapply match_sm_wd23; eauto).
  destruct A1; destruct A2; destruct A3; try contradiction.
+ (*midstep_to_atExt*)
  rename c into c1'. rename m into m1'. rename e into f. rename l into vals1.
  rename c0 into c2'. rename m0 into m2'. rename e0 into f2. rename l0 into vals2.
  rename c4 into c3'. rename m4 into m3'. rename e1 into f3. rename l1 into vals3.
  rename b into W1. rename b0 into W2. rename b1 into W3. 

  exists (cd2, Some c2', cd3), (compose_sm mu12' mu23'). 
  split; [ solve [trivial] | ].
  split; [ solve [ apply compose_sm_intern_incr; trivial] | ].
  destruct REL12 as [SMV12' [WD12' (*MS12'*) [Minj12' [F12 [MRR1 [MRR2 [ARGS12 X12]]]]]]]; subst f2.
  destruct REL23 as [SMV23' [WD23' (*MS23'*) [Minj23' [F23 [_ [MRR3 [ARGS23 X23]]]]]]]; subst f3.
  assert (INV': locBlocksSrc mu12' = (fun b => locBlocksSrc mu12 b || freshloc m1 m1' b) /\
                locBlocksTgt mu23' = (fun b => locBlocksTgt mu23 b || freshloc m3 m3' b) /\
                extBlocksSrc mu12' = extBlocksSrc mu12 /\
                extBlocksTgt mu23' = extBlocksTgt mu23).
  { clear - LOCALLOC12 LOCALLOC23.
    destruct mu12; destruct mu12'; destruct mu23; destruct mu23'.
    simpl in *; intuition. }
  (*split. admit. globals_separate*)
  split; [ trivial | ]. (*solves LOCALLOC13'*)

  assert (L: locBlocksTgt mu12' = locBlocksSrc mu23').
    { clear INV' ARGS12 ARGS23.
               simpl in LOCALLOC12. simpl in LOCALLOC23.
               destruct mu12; destruct mu12'; destruct mu23; destruct mu23'; simpl in *.
               destruct LOCALLOC12 as [? [QQ [? ?]]]; rewrite QQ.
               destruct LOCALLOC23 as [WW [? [? ?]]]; rewrite WW.
               red in INV; simpl in INV; intuition; subst; trivial. }
  assert (E: extBlocksTgt mu12' = extBlocksSrc mu23').
    { simpl in LOCALLOC12. red in LOCALLOC12.
               simpl in LOCALLOC23. red in LOCALLOC23. 
               destruct mu12; destruct mu12'; destruct mu23; destruct mu23'; simpl in *.
               destruct INV' as [? [? [? ?]]].
               red in INV; simpl in INV; intuition; subst; trivial. } 

  assert (Pub: forall b, pubBlocksTgt mu12' b = true -> pubBlocksSrc mu23' b = true).
  { destruct INC12 as [? [? [? [? [? [P ?]]]]]]. rewrite <- P. 
    destruct INC23 as [? [? [? [? [Q ?]]]]]. rewrite <- Q. apply INV. }
  assert (Frgn: forall b, frgnBlocksTgt mu12' b = true -> frgnBlocksSrc mu23' b = true).
  { destruct INC12 as [? [? [? [? [? [? [? [F ?]]]]]]]]. rewrite <- F. 
    destruct INC23 as [? [? [? [? [? [? [G ?]]]]]]]. rewrite <- G. apply INV. }
  assert (WDmu': SM_wd (compose_sm mu12' mu23')) by (apply compose_sm_wd; trivial).
  assert (SMVmu': sm_valid (compose_sm mu12' mu23') m1' m3') by (eapply compose_sm_valid; eauto).
  
  split.
  - (*MST_relate*)
    split; trivial. 
    split; trivial. 
    split.
    { clear X12 X23 CONF12 CONF23.
      rewrite compose_sm_as_inj; trivial. 
      eapply Mem.inject_compose; eassumption. }
    split; [ trivial | ].
    split; [ trivial | ].
    split; [ trivial | ].
    split. { (*val_inject arg1 args3*) 
             rewrite compose_sm_as_inj; try eauto.
             rewrite restrict_compose, vis_compose_sm; simpl. 
             eapply forall_val_inject_compose; try eassumption.
             eapply forall_vals_inject_restrictD; eassumption. }
    rewrite compose_sm_exportedSrc, compose_sm_exportedTgt; trivial.
    intros ? ? PS PT ? NU.
    destruct (X12 _ _ (eq_refl _) (eq_refl _) _ (eq_refl _)) as [MCC12 INJJ12]; clear X12.
    destruct (X23 _ _ (eq_refl _) (eq_refl _) _ (eq_refl _)) as [MCC23 INJJ23]; clear X23.

    assert (HREACH: forall b2, REACH m2' (exportedTgt mu12' vals2) b2 = true -> 
                               REACH m2' (exportedSrc mu23' vals2) b2 = true).
    { intros. eapply REACH_mono; [| eassumption].
      unfold exportedTgt, exportedSrc, sharedTgt; intros bb X.
      apply orb_true_iff in X; destruct X as [X | X].
      rewrite X; trivial.
      apply orb_true_iff. right.
      apply orb_true_iff in X; destruct X as [X | X].
      apply frgnSrc_shared; trivial. apply Frgn; trivial.
      apply pubSrc_shared; trivial. apply Pub; trivial. } 
    assert (WDnu: SM_wd nu).
    { subst nu. apply replace_locals_wd; trivial.  
      + subst; intros b X; apply andb_true_iff in X; destruct X as [X1 X2].
        exploit REACH_local_REACH; [ apply WD12' | | | apply X2 | apply X1| ]. eassumption.
        eapply forall_vals_inject_restrictD; eassumption.
        intros [b2 [d1 [LOC12 R12]]]. 
        destruct (local_DomRng _ WD12' _ _ _ LOC12) as [L1 L2]; rewrite L in L2.
        exploit REACH_local_REACH; [ apply WD23' | | | | apply L2 |].
        { eassumption. }
        { eapply forall_vals_inject_restrictD; eassumption. }
        { auto. }
        intros [b3 [d2 [LOC23 R23]]]. 
        destruct (local_DomRng _ WD23' _ _ _ LOC23) as [_ L3].
        exists b3, (d1+d2). 
        erewrite compose_sm_local, compose_meminjI_Some, R23, andb_true_r; [| eassumption|eassumption].
        split; trivial.
      + subst; intros b X. apply andb_true_iff in X; apply X. }
    split. 
    { (*MatchState*) red. exists c2', m2'. eexists; eexists; split. trivial.
      split; [ | split; [ | split; eassumption]].
      + subst. destruct mu12'; destruct mu23'; unfold compose_sm; simpl in *; trivial. 
      + red. simpl. rewrite replace_locals_locBlocksSrc, replace_locals_extBlocksSrc, replace_locals_pubBlocksSrc, replace_locals_frgnBlocksSrc.
        rewrite L, replace_locals_locBlocksTgt, replace_locals_extBlocksTgt, replace_locals_pubBlocksTgt, replace_locals_frgnBlocksTgt.
        repeat split; trivial.
        intros bb X. apply andb_true_iff. 
        apply andb_true_iff in X. destruct X as [X1 X2]. split; [ trivial | auto]. }
        eapply (inject_shared_replace_locals _ _ (compose_sm mu12' mu23') vals1 vals3); try reflexivity; trivial.
        { rewrite vis_compose_sm.
          apply match_visible in MCC12. unfold vis in *.
          rewrite replace_locals_locBlocksSrc, replace_locals_frgnBlocksSrc in MCC12; trivial. }
        { rewrite compose_sm_as_inj; trivial; eapply Mem.inject_compose; eassumption. }
        { subst; rewrite compose_sm_exportedSrc; trivial. }

  - (*confinement*)
    clear - CONF12 CONF23 INV WD12 WD23. eapply compose_sm_confined; eassumption.

+ (*case RET*)
  simpl in *. rename b into W1. rename b0 into W2. rename b1 into W3.
  rename c4 into c3'. rename m4 into m3'. rename v1 into v3.
  rename c into c'. rename m into m1'. rename v into v1.
  rename c0 into c2'. rename m0 into m2'. rename v0 into v2.
  exists (cd2, Some c2', cd3), (compose_sm mu12' mu23').
  split; [ trivial |].
  split. apply compose_sm_intern_incr; trivial.
  destruct REL12 as [SMV12' [WD12' [Minj12' [MRR1 [MRR2 RV12]]]]].
  destruct REL23 as [SMV23' [WD23' [Minj23' [MRR_ [MRR3 RV23]]]]]. 
  assert (INV': locBlocksSrc mu12' = (fun b => locBlocksSrc mu12 b || freshloc m1 m1' b) /\
                locBlocksTgt mu23' = (fun b => locBlocksTgt mu23 b || freshloc m3 m3' b) /\
                extBlocksSrc mu12' = extBlocksSrc mu12 /\
                extBlocksTgt mu23' = extBlocksTgt mu23).
  { clear - LOCALLOC12 LOCALLOC23.
    destruct mu12; destruct mu12'; destruct mu23; destruct mu23'.
    simpl in *; intuition. }

  assert (Pub: forall b, pubBlocksTgt mu12' b = true -> pubBlocksSrc mu23' b = true).
  { destruct INC12 as [? [? [? [? [? [P ?]]]]]]. rewrite <- P. 
    destruct INC23 as [? [? [? [? [Q ?]]]]]. rewrite <- Q. apply INV. }
  assert (Frgn: forall b, frgnBlocksTgt mu12' b = true -> frgnBlocksSrc mu23' b = true).
  { destruct INC12 as [? [? [? [? [? [? [? [F ?]]]]]]]]. rewrite <- F. 
    destruct INC23 as [? [? [? [? [? [? [G ?]]]]]]]. rewrite <- G. apply INV. }

  assert (WDmu': SM_wd (compose_sm mu12' mu23')) by (apply compose_sm_wd; trivial).
  assert (SMVmu': sm_valid (compose_sm mu12' mu23') m1' m3') by (eapply compose_sm_valid; eauto).
  
  split. { unfold compose_sm; simpl; trivial. }

  assert (L: locBlocksTgt mu12' = locBlocksSrc mu23').
  { clear - INV LOCALLOC12 LOCALLOC23.
               simpl in LOCALLOC12. simpl in LOCALLOC23.
               destruct mu12; destruct mu12'; destruct mu23; destruct mu23'; simpl in *.
               destruct LOCALLOC12 as [? [QQ [? ?]]]; rewrite QQ.
               destruct LOCALLOC23 as [WW [? [? ?]]]; rewrite WW.
               red in INV; simpl in INV; intuition; subst; trivial. }
    assert (E: extBlocksTgt mu12' = extBlocksSrc mu23').
    {  clear - INV' INV LOCALLOC12 LOCALLOC23.
       simpl in LOCALLOC12. red in LOCALLOC12.
               simpl in LOCALLOC23. red in LOCALLOC23. 
               destruct mu12; destruct mu12'; destruct mu23; destruct mu23'; simpl in *.
               destruct INV' as [? [? [? ?]]].
               red in INV; simpl in INV; intuition; subst; trivial. } 
  split.
  - split; [ trivial | ].
    split; [ trivial | ].
    split.
    { clear CONF12 CONF23.
      rewrite compose_sm_as_inj; trivial. 
      eapply Mem.inject_compose; eassumption. }
    split; [ trivial | ].
    split; [ trivial | ].
    (*val_inject arg1 args3*) 
    clear - RV12 RV23 WD12' WD23' L E.
             rewrite compose_sm_as_inj; try eauto.
             rewrite restrict_compose, vis_compose_sm; simpl. 
             eapply val_inject_compose; try eassumption.
             eapply val_inject_incr. apply restrict_incr; eauto. eassumption.
  - (*confinement*)
    clear - CONF12 CONF23 INV WD12 WD23. eapply compose_sm_confined; eassumption.

+ (*case DIV*)
  simpl in *. rename P into W1. rename P0 into W2. rename P1 into W3.
  unfold coreData; simpl. exists (cd2, Some c2, cd3), (compose_sm mu12' mu23').
  intuition.
  - apply compose_sm_intern_incr; trivial.
  - eapply compose_sm_confined; eassumption.
Qed.

Lemma Transitivity: SM_simulation_inject Sem1 Sem3 ge1 ge3.
Proof. (*
specialize (match_midstep _ _ _ _ SIM12); intros Diag12.
specialize (match_midstep _ _ _ _ SIM23); intros Diag23.*)
eapply (Build_SM_simulation_inject Sem1 Sem3 ge1 ge3 coreData MatchState).
+ eapply well_founded_sem_compose_ord_eq_eq.
  apply (core_ord_wf Sem1 Sem2 ge1 ge2 SIM12).
  apply (core_ord_wf Sem2 Sem3 ge2 ge3 SIM23).
+ intros. rename c2 into c3. rename m2 into m3.
  destruct d as [[d12 X] d23]. simpl in H.
  destruct H as [c2 [m2 [mu12 [mu23 [? [? [INV [MS12 MS23]]]]]]]]; subst.
  apply match_sm_wd in MS12. apply match_sm_wd in MS23.
  destruct INV as [INVa [INVb [INVc INVd]]].
  apply compose_sm_wd; trivial. 
+ admit. (*genvs_domain_eq*)
+ admit. (*gloabls stuff*)
+ intros. rename c2 into c3. rename m2 into m3.
  destruct d as [[d12 X] d23]. simpl in H.
  destruct H as [c2 [m2 [mu12 [mu23 [? [? [INV [MS12 MS23]]]]]]]]; subst.
  rewrite vis_compose_sm. eapply SIM12. apply MS12. 
+ intros. rename c2 into c3. rename m2 into m3.
  destruct d as [[d12 X] d23]. simpl in H.
  destruct H as [c2 [m2 [mu12 [mu23 [? [? [INV [MS12 MS23]]]]]]]]; subst.
  eapply compose_sm_valid. eapply SIM12; eauto. eapply SIM23; eauto.
+ admit. (*initcore*)
+ apply diagram_trans.
+ admit. (*afterexternal*)
Admitted.

End TRANS.
End SM_TRANSITIVITY.

Section SIMPLE_TRANSITIVITY. Section TRANS.

Context
  {F1 V1 C1 F2 V2 C2 F3 V3 C3: Type}
  (Sem1 : @EffectSem (Genv.t F1 V1) C1)
  (Sem2 : @EffectSem (Genv.t F2 V2) C2)
  (Sem3 : @EffectSem (Genv.t F3 V3) C3)
  (ge1 : Genv.t F1 V1)
  (ge2 : Genv.t F2 V2)
  (ge3 : Genv.t F3 V3).

Variable SIM12:Simple_simulation_inject Sem1 Sem2 ge1 ge2.
Definition MatchState12:= Smatch_state _ _ _ _ SIM12.
Definition match_sm_wd12:= Smatch_sm_wd _ _ _ _ SIM12.

Variable SIM23:Simple_simulation_inject Sem2 Sem3 ge2 ge3.
Definition MatchState23:= Smatch_state _ _ _ _ SIM23.
Definition match_sm_wd23:= Smatch_sm_wd _ _ _ _ SIM23.

Definition MatchState (mu: SM_Injection) (c1:C1)(m1:mem)(c3:C3)(m3:mem): Prop :=
        exists c2, exists m2, exists mu1, exists mu2,
          mu = compose_sm mu1 mu2 /\ muINV mu1 mu2 /\
          MatchState12 mu1 c1 m1 c2 m2 /\ MatchState23 mu2 c2 m2 c3 m3.

Lemma diagram_trans:
forall (mu : SM_Injection) (c1 : C1) (m1 : mem) 
  (c3 : C3) (m3 : mem) (A1 : MidStepTrackResult),
  MatchState mu c1 m1 c3 m3 ->
  midstepT Sem1 ge1 c1 m1 A1 ->
exists (A3 : MidStepTrackResult) (mu' mu'': SM_Injection) FS FT,
  midstepT Sem3 ge3 c3 m3 A3 /\
  intern_incr mu mu' /\ pubincr mu' FS FT mu'' /\
  (*  globals_separate ge3 mu mu' /\*)
  MST_locally_allocated mu mu' m1 m3 A1 A3 /\
  MST_relate ge1 ge3 MatchState mu'' A1 A3 /\
  confined (Wset A1) (Wset A3) mu.
Proof. intros. rename H0 into STEP1.
  destruct H as [c2 [m2 [mu12 [mu23 [? [INV [MS12 MS23]]]]]]]; subst.
  destruct (Smatch_midstep _ _ _ _ SIM12 _ _ _ _ _ _ MS12 STEP1)
   as [A2 [mu12' [mu12'' [PS1 [PT2 [STEP2 [INC12 [PINCR12 [LOCALLOC12 [REL12 CONF12]]]]]]]]]].
  destruct (Smatch_midstep _ _ _ _ SIM23 _ _ _ _ _ _ MS23 STEP2)
   as [A3 [mu23' [mu23'' [PS2 [PT3 [STEP3 [INC23 [PINCR23 [LOCALLOC23 [REL23 CONF23]]]]]]]]]].
  exists A3.
  assert (WD12: SM_wd mu12) by (eapply match_sm_wd12; eauto).
  assert (WD23: SM_wd mu23) by (eapply match_sm_wd23; eauto).
  destruct A1; destruct A2; destruct A3; try contradiction.
+ (*midstep_to_atExt*)
  rename c into c1'. rename m into m1'. rename e into f. rename l into vals1.
  rename c0 into c2'. rename m0 into m2'. rename e0 into f2. rename l0 into vals2.
  rename c4 into c3'. rename m4 into m3'. rename e1 into f3. rename l1 into vals3.
  rename b into W1. rename b0 into W2. rename b1 into W3. 

  exists (compose_sm mu12' mu23'), (compose_sm mu12'' mu23''). 
  exists PS1, PT3.
  split; [ solve [trivial] | ].
  split; [ solve [ apply compose_sm_intern_incr; trivial] | ].
  split. { clear - PINCR12 PINCR23. unfold pubincr in *. 
           destruct mu12'; destruct mu12''; destruct mu23'; destruct mu23''; simpl in *.
           intuition. rewrite H, H1; trivial. rewrite H3, H0; trivial. }
  destruct REL12 as [SMV12' [WD12' (*MS12'*) [Minj12' [F12 [MRR1 [MRR2 [ARGS12 X12]]]]]]]; subst f2.
  destruct REL23 as [SMV23' [WD23' (*MS23'*) [Minj23' [F23 [_ [MRR3 [ARGS23 X23]]]]]]]; subst f3.
  assert (INV': locBlocksSrc mu12' = (fun b => locBlocksSrc mu12 b || freshloc m1 m1' b) /\
                locBlocksTgt mu23' = (fun b => locBlocksTgt mu23 b || freshloc m3 m3' b) /\
                extBlocksSrc mu12' = extBlocksSrc mu12 /\
                extBlocksTgt mu23' = extBlocksTgt mu23).
  { clear - LOCALLOC12 LOCALLOC23.
    destruct mu12; destruct mu12'; destruct mu23; destruct mu23'.
    simpl in *; intuition. }
  (*split. admit. globals_separate*)
  split; [ trivial | ]. (*solves LOCALLOC13'*)

  assert (L: locBlocksTgt mu12' = locBlocksSrc mu23').
    { clear INV' ARGS12 ARGS23.
               simpl in LOCALLOC12. simpl in LOCALLOC23.
               destruct mu12; destruct mu12'; destruct mu23; destruct mu23'; simpl in *.
               destruct LOCALLOC12 as [? [QQ [? ?]]]; rewrite QQ.
               destruct LOCALLOC23 as [WW [? [? ?]]]; rewrite WW.
               red in INV; simpl in INV; intuition; subst; trivial. }
  assert (E: extBlocksTgt mu12' = extBlocksSrc mu23').
    { simpl in LOCALLOC12. red in LOCALLOC12.
               simpl in LOCALLOC23. red in LOCALLOC23. 
               destruct mu12; destruct mu12'; destruct mu23; destruct mu23'; simpl in *.
               destruct INV' as [? [? [? ?]]].
               red in INV; simpl in INV; intuition; subst; trivial. } 

  assert (Pub: forall b, pubBlocksTgt mu12' b = true -> pubBlocksSrc mu23' b = true).
  { destruct INC12 as [? [? [? [? [? [P ?]]]]]]. rewrite <- P. 
    destruct INC23 as [? [? [? [? [Q ?]]]]]. rewrite <- Q. apply INV. }
  assert (Frgn: forall b, frgnBlocksTgt mu12' b = true -> frgnBlocksSrc mu23' b = true).
  { destruct INC12 as [? [? [? [? [? [? [? [F ?]]]]]]]]. rewrite <- F. 
    destruct INC23 as [? [? [? [? [? [? [G ?]]]]]]]. rewrite <- G. apply INV. }
  assert (WDmu'': SM_wd (compose_sm mu12'' mu23'')).
  { apply compose_sm_wd; trivial.
clear - PINCR12 PINCR23. intros. unfold pubincr in *. intuition.
rewrite H9. rewrite H10 in H.
apply orb_true_iff in H. destruct H. admit. rewrite H.
 erewrite PINCR23.
destruct mu12'; destruct mu23'; 
destruct mu12''; destruct mu23''; simpl in *.
 PS
  assert (SMVmu': sm_valid (compose_sm mu12' mu23') m1' m3') by (eapply compose_sm_valid; eauto).
  
  split.
  - (*MST_relate*)
    split; trivial. 
    split; trivial. 
    split.
    { clear X12 X23 CONF12 CONF23.
      rewrite compose_sm_as_inj; trivial. 
      eapply Mem.inject_compose; eassumption. }
    split; [ trivial | ].
    split; [ trivial | ].
    split; [ trivial | ].
    split. { (*val_inject arg1 args3*) 
             rewrite compose_sm_as_inj; try eauto.
             rewrite restrict_compose, vis_compose_sm; simpl. 
             eapply forall_val_inject_compose; try eassumption.
             eapply forall_vals_inject_restrictD; eassumption. }
    rewrite compose_sm_exportedSrc, compose_sm_exportedTgt; trivial.
    intros ? ? PS PT ? NU.
    destruct (X12 _ _ (eq_refl _) (eq_refl _) _ (eq_refl _)) as [MCC12 INJJ12]; clear X12.
    destruct (X23 _ _ (eq_refl _) (eq_refl _) _ (eq_refl _)) as [MCC23 INJJ23]; clear X23.

    assert (HREACH: forall b2, REACH m2' (exportedTgt mu12' vals2) b2 = true -> 
                               REACH m2' (exportedSrc mu23' vals2) b2 = true).
    { intros. eapply REACH_mono; [| eassumption].
      unfold exportedTgt, exportedSrc, sharedTgt; intros bb X.
      apply orb_true_iff in X; destruct X as [X | X].
      rewrite X; trivial.
      apply orb_true_iff. right.
      apply orb_true_iff in X; destruct X as [X | X].
      apply frgnSrc_shared; trivial. apply Frgn; trivial.
      apply pubSrc_shared; trivial. apply Pub; trivial. } 
    assert (WDnu: SM_wd nu).
    { subst nu. apply replace_locals_wd; trivial.  
      + subst; intros b X; apply andb_true_iff in X; destruct X as [X1 X2].
        exploit REACH_local_REACH; [ apply WD12' | | | apply X2 | apply X1| ]. eassumption.
        eapply forall_vals_inject_restrictD; eassumption.
        intros [b2 [d1 [LOC12 R12]]]. 
        destruct (local_DomRng _ WD12' _ _ _ LOC12) as [L1 L2]; rewrite L in L2.
        exploit REACH_local_REACH; [ apply WD23' | | | | apply L2 |].
        { eassumption. }
        { eapply forall_vals_inject_restrictD; eassumption. }
        { auto. }
        intros [b3 [d2 [LOC23 R23]]]. 
        destruct (local_DomRng _ WD23' _ _ _ LOC23) as [_ L3].
        exists b3, (d1+d2). 
        erewrite compose_sm_local, compose_meminjI_Some, R23, andb_true_r; [| eassumption|eassumption].
        split; trivial.
      + subst; intros b X. apply andb_true_iff in X; apply X. }
    split. 
    { (*MatchState*) red. exists c2', m2'. eexists; eexists.
      split; [ | split; [ | split; eassumption]].
      + subst. destruct mu12'; destruct mu23'; unfold compose_sm; simpl in *; trivial. 
      + red. simpl. rewrite replace_locals_locBlocksSrc, replace_locals_extBlocksSrc, replace_locals_pubBlocksSrc, replace_locals_frgnBlocksSrc.
        rewrite L, replace_locals_locBlocksTgt, replace_locals_extBlocksTgt, replace_locals_pubBlocksTgt, replace_locals_frgnBlocksTgt.
        repeat split; trivial.
        intros bb X. apply andb_true_iff. 
        apply andb_true_iff in X. destruct X as [X1 X2]. split; [ trivial | auto]. }
        eapply (inject_shared_replace_locals _ _ (compose_sm mu12' mu23') vals1 vals3); try reflexivity; trivial.
        { rewrite vis_compose_sm.
          apply Smatch_visible in MCC12. unfold vis in *.
          rewrite replace_locals_locBlocksSrc, replace_locals_frgnBlocksSrc in MCC12; trivial. }
        { rewrite compose_sm_as_inj; trivial; eapply Mem.inject_compose; eassumption. }
        { subst; rewrite compose_sm_exportedSrc; trivial. }

  - (*confinement*)
    clear - CONF12 CONF23 INV WD12 WD23. eapply compose_sm_confined; eassumption.

+ (*case RET*)
  simpl in *. rename b into W1. rename b0 into W2. rename b1 into W3.
  rename c4 into c3'. rename m4 into m3'. rename v1 into v3.
  rename c into c'. rename m into m1'. rename v into v1.
  rename c0 into c2'. rename m0 into m2'. rename v0 into v2.
  exists (compose_sm mu12' mu23').
  split; [ trivial |].
  split. apply compose_sm_intern_incr; trivial.
  destruct REL12 as [SMV12' [WD12' [Minj12' [MRR1 [MRR2 RV12]]]]].
  destruct REL23 as [SMV23' [WD23' [Minj23' [MRR_ [MRR3 RV23]]]]]. 
  assert (INV': locBlocksSrc mu12' = (fun b => locBlocksSrc mu12 b || freshloc m1 m1' b) /\
                locBlocksTgt mu23' = (fun b => locBlocksTgt mu23 b || freshloc m3 m3' b) /\
                extBlocksSrc mu12' = extBlocksSrc mu12 /\
                extBlocksTgt mu23' = extBlocksTgt mu23).
  { clear - LOCALLOC12 LOCALLOC23.
    destruct mu12; destruct mu12'; destruct mu23; destruct mu23'.
    simpl in *; intuition. }

  assert (Pub: forall b, pubBlocksTgt mu12' b = true -> pubBlocksSrc mu23' b = true).
  { destruct INC12 as [? [? [? [? [? [P ?]]]]]]. rewrite <- P. 
    destruct INC23 as [? [? [? [? [Q ?]]]]]. rewrite <- Q. apply INV. }
  assert (Frgn: forall b, frgnBlocksTgt mu12' b = true -> frgnBlocksSrc mu23' b = true).
  { destruct INC12 as [? [? [? [? [? [? [? [F ?]]]]]]]]. rewrite <- F. 
    destruct INC23 as [? [? [? [? [? [? [G ?]]]]]]]. rewrite <- G. apply INV. }

  assert (WDmu': SM_wd (compose_sm mu12' mu23')) by (apply compose_sm_wd; trivial).
  assert (SMVmu': sm_valid (compose_sm mu12' mu23') m1' m3') by (eapply compose_sm_valid; eauto).
  
  split. { unfold compose_sm; simpl; trivial. }

  assert (L: locBlocksTgt mu12' = locBlocksSrc mu23').
  { clear - INV LOCALLOC12 LOCALLOC23.
               simpl in LOCALLOC12. simpl in LOCALLOC23.
               destruct mu12; destruct mu12'; destruct mu23; destruct mu23'; simpl in *.
               destruct LOCALLOC12 as [? [QQ [? ?]]]; rewrite QQ.
               destruct LOCALLOC23 as [WW [? [? ?]]]; rewrite WW.
               red in INV; simpl in INV; intuition; subst; trivial. }
    assert (E: extBlocksTgt mu12' = extBlocksSrc mu23').
    {  clear - INV' INV LOCALLOC12 LOCALLOC23.
       simpl in LOCALLOC12. red in LOCALLOC12.
               simpl in LOCALLOC23. red in LOCALLOC23. 
               destruct mu12; destruct mu12'; destruct mu23; destruct mu23'; simpl in *.
               destruct INV' as [? [? [? ?]]].
               red in INV; simpl in INV; intuition; subst; trivial. } 
  split.
  - split; [ trivial | ].
    split; [ trivial | ].
    split.
    { clear CONF12 CONF23.
      rewrite compose_sm_as_inj; trivial. 
      eapply Mem.inject_compose; eassumption. }
    split; [ trivial | ].
    split; [ trivial | ].
    (*val_inject arg1 args3*) 
    clear - RV12 RV23 WD12' WD23' L E.
             rewrite compose_sm_as_inj; try eauto.
             rewrite restrict_compose, vis_compose_sm; simpl. 
             eapply val_inject_compose; try eassumption.
             eapply val_inject_incr. apply restrict_incr; eauto. eassumption.
  - (*confinement*)
    clear - CONF12 CONF23 INV WD12 WD23. eapply compose_sm_confined; eassumption.

+ (*case DIV*)
  simpl in *. rename P into W1. rename P0 into W2. rename P1 into W3.
  exists (compose_sm mu12' mu23').
  intuition.
  - apply compose_sm_intern_incr; trivial.
  - eapply compose_sm_confined; eassumption.
Qed.

Lemma Transitivity: Simple_simulation_inject Sem1 Sem3 ge1 ge3.
Proof.
eapply (Build_Simple_simulation_inject Sem1 Sem3 ge1 ge3 MatchState).
+ intros. rename c2 into c3. rename m2 into m3.
  destruct H as [c2 [m2 [mu12 [mu23 [? [INV [MS12 MS23]]]]]]]; subst.
  apply Smatch_sm_wd in MS12. apply Smatch_sm_wd in MS23.
  destruct INV as [INVa [INVb [INVc INVd]]].
  apply compose_sm_wd; trivial.
+ admit. (*genvs_domain_eq*)
+ admit. (*gloabls stuff*)
+ intros. rename c2 into c3. rename m2 into m3.
  destruct H as [c2 [m2 [mu12 [mu23 [? [INV [MS12 MS23]]]]]]]; subst.
  rewrite vis_compose_sm. eapply SIM12. apply MS12. 
+ intros. rename c2 into c3. rename m2 into m3.
  destruct H as [c2 [m2 [mu12 [mu23 [? [INV [MS12 MS23]]]]]]]; subst.
  eapply compose_sm_valid. eapply SIM12; eauto. eapply SIM23; eauto.
+ admit. (*initcore*)
+ apply diagram_trans.
+ admit. (*afterexternal*)
Admitted.

End TRANS. End SIMPLE_TRANSITIVITY.