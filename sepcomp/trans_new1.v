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

Import SM_simulation.
(*
Axiom mudec: forall mu m1 m2, SM_wd mu -> sm_valid mu m1 m2 ->
forall b2, {exists b1 d, Mem.valid_block m1 b1 /\ as_inj mu b1 = Some(b2,d)} +
           {~ exists b1 d, Mem.valid_block m1 b1 /\ as_inj mu b1 = Some(b2,d)}.
*)
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
  (c3 : C3) (m3 : mem) (A1 : MidStepResult),
MatchState d mu c1 m1 c3 m3 ->
midstep Sem1 ge1 c1 m1 A1 ->
exists (A3 : MidStepResult) (cd' : coreData) (mu' : SM_Injection),
  midstep Sem3 ge3 c3 m3 A3 /\
  intern_incr mu mu' /\
  globals_separate ge3 mu mu' /\
  MSR_locally_allocated mu mu' m1 m3 A1 A3 /\
  MSR_relate ge1 ge3 (MatchState cd') mu' A1 A3 /\
  MSR_confined mu m1 m3 A3 (*
  (MSR_unchanged_on (fun (b : block) (_ : Z) => vis mu b = false) m1 A1 ->
   MSR_unchanged_on (extern_out_of_reach mu m1) m2 A2)*).
Proof. intros. rename H0 into STEP1.
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
  rename c into c1'. rename m into m1'. rename e into f. rename l into vals1.
  rename c0 into c2'. rename m0 into m2'. rename e0 into f2. rename l0 into vals2.
  rename c4 into c3'. rename m4 into m3'. rename e1 into f3. rename l1 into vals3.
  exists (cd2, Some c2', cd3), (compose_sm mu12' mu23'). 
  split; [ solve [trivial] | ].
  split; [ solve [ apply compose_sm_intern_incr; trivial] | ].
  destruct REL12 as [Minj12' [F12 [MRR1 [MRR2 [ARGS12 X12]]]]]; subst f2.
  destruct REL23 as [Minj23' [F23 [_ [MRR3 [ARGS23 X23]]]]]; subst f3.
(*  simpl.*)
  assert (INV': locBlocksSrc mu12' = (fun b => locBlocksSrc mu12 b || freshloc m1 m1' b) /\
                locBlocksTgt mu23' = (fun b => locBlocksTgt mu23 b || freshloc m3 m3' b) /\
                extBlocksSrc mu12' = extBlocksSrc mu12 /\
                extBlocksTgt mu23' = extBlocksTgt mu23).
  { clear - LOCALLOC12 LOCALLOC23.
    destruct mu12; destruct mu12'; destruct mu23; destruct mu23'.
    simpl in *; intuition. }
  split. admit. (*globals_separate*)
  split; [ trivial | ].
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
    split. { (*val_inject arg1 args3*) 
             rewrite compose_sm_as_inj; try eauto.
             rewrite restrict_compose, vis_compose_sm; simpl. 
             eapply forall_val_inject_compose; try eassumption.
             eapply forall_vals_inject_restrictD; eassumption. }
  assert (Pub: forall b, pubBlocksTgt mu12' b = true -> pubBlocksSrc mu23' b = true).
  { destruct INC12 as [? [? [? [? [? [P ?]]]]]]. rewrite <- P. 
    destruct INC23 as [? [? [? [? [Q ?]]]]]. rewrite <- Q. apply INV. }
  assert (Frgn: forall b, frgnBlocksTgt mu12' b = true -> frgnBlocksSrc mu23' b = true).
  { destruct INC12 as [? [? [? [? [? [? [? [F ?]]]]]]]]. rewrite <- F. 
    destruct INC23 as [? [? [? [? [? [? [G ?]]]]]]]. rewrite <- G. apply INV. }
  rewrite compose_sm_exportedSrc, compose_sm_exportedTgt; trivial.
  intros ? ? PS PT ? NU. 
  destruct (X12 _ _ (eq_refl _) (eq_refl _) _ (eq_refl _)) as [MCC12 INJJ12]; clear X12.
  destruct (X23 _ _ (eq_refl _) (eq_refl _) _ (eq_refl _)) as [MCC23 INJJ23]; clear X23.  
  assert (WDmu123': SM_wd (compose_sm mu12' mu23')).
  { apply compose_sm_wd; trivial. }
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
 - (*confined
   simpl. clear X12 X23 INV' ARGS12 ARGS23. simpl in * (*UNCH2, UNCH3*).
   intros b3 z VB3; simpl.
   destruct (UNCH3 _ z VB3) as [U2 | [ LT2 | [b2 [d2 [FRG23 Perm2]]]]].
   left; trivial.
   right; left; trivial.
   assert (VB2 := Mem.perm_valid_block _ _ _ _ _ Perm2).
   destruct (UNCH2 _ (z-d2) VB2) as [U2 | [ LT2 | [b1 [d1 [FRG12 Perm1]]]]].*)
   simpl. clear X12 X23 INV' ARGS12 ARGS23. simpl in * (*UNCH2, UNCH3*).
   assert (Minj12:= match_inject _ _ _ _ SIM12 _ _ _ _ _ _ MS12).
   assert (Minj23:= match_inject _ _ _ _ SIM23 _ _ _ _ _ _ MS23).
   intros b3 z ET3; simpl in *.
   destruct (UNCH3 _ z ET3) as [U2 | [b2 [d2 [FRG23 Perm2]]]].
   left; trivial.
   destruct (UNCH2 b2 (z-d2)) as [U2 | [b1 [d1 [FRG12 Perm1]]]].
   { destruct INV as [INVa [INVb [INVc INVd]]]; rewrite INVb.
     eapply foreign_DomRng; eassumption. }
   { left. (*inv U1.*) inv STEP3.
     specialize (Mem.mi_perm_inv _ _ _ Minj23' b2 (z - d2) b3 d2); intros PINV23'.
     specialize (Mem.mi_perm_inv _ _ _ Minj23 b2 (z - d2) b3 d2); intros PINV23.
     assert (AI23: as_inj mu23 b2 = Some (b3, d2)) by (apply foreign_in_all in FRG23; trivial).
     assert (AI23': as_inj mu23' b2 = Some (b3, d2)) by (eapply intern_incr_as_inj; eauto).
     rewrite Z.sub_simpl_r in PINV23, PINV23'.
     assert (PERM: forall k p, Mem.valid_block m3 b3 ->
                 Mem.perm m3 b3 z k p <-> Mem.perm m3' b3 z k p).
     { intros.
       assert (VB2:= Mem.perm_valid_block _ _ _ _ _ Perm2).
       specialize (PINV23' k p AI23'). specialize (PINV23 k p AI23).
       split; intros P.
       - destruct (PINV23 P); [ clear PINV23 | contradiction].
         specialize (Mem.perm_inject _ _ _ _ _ _ (z-d2) k p AI23' Minj23'). 
         rewrite Z.sub_simpl_r; intros X; apply X; clear X.
         apply U2; trivial. 
       - destruct (PINV23' P); clear PINV23' PINV23. 
         * specialize (Mem.perm_inject _ _ _ _ _ _ (z-d2) k p AI23 Minj23). 
           rewrite Z.sub_simpl_r; intros X; apply X; clear X.
           apply U2; trivial.
         * elim H0; clear H0. apply U2; trivial. }
     constructor.
     + apply mem_forward_nextblock. eapply corestep_star_fwd; eassumption.
     + intros. symmetry in H; inv H. eauto.
     + intros. symmetry in H; inv H.
       assert (VB2:= Mem.perm_valid_block _ _ _ _ _ Perm2).
       specialize (PINV23' Cur Readable AI23'). specialize (PINV23 Cur Readable AI23).
       destruct (PINV23 H0) as [P2 |]; [ | contradiction].
       assert (P2': Mem.perm m2' b2 (z - d2) Cur Readable) by (eapply U2; trivial).
       assert (MI23 :=Mem.mi_memval _ _ _ (Mem.mi_inj _ _ _ Minj23) _ _ _ _ AI23 P2).
       assert (MI23' :=Mem.mi_memval _ _ _ (Mem.mi_inj _ _ _ Minj23') _ _ _ _ AI23' P2').
       assert (Cont2: ZMap.get (z - d2) (Mem.mem_contents m2') !! b2 =
                      ZMap.get (z - d2) (Mem.mem_contents m2) !! b2) by (apply U2; trivial).
       rewrite Cont2 in MI23'.
       eapply memval_inject_incr in MI23. 2: eapply intern_incr_as_inj; eassumption.
       clear Cont2. remember (ZMap.get z (Mem.mem_contents m3) !! b3) as v.
       inv  MI23; inv MI23'. 
       - rewrite <- H2 in *. inv H5. rewrite Z.sub_simpl_r in H, H6. congruence. 
       - rewrite <- H2 in *. inv H3.
       - rewrite <- H2 in H5; inv H5.
       - rewrite <- H in H6; inv H6.
       - rewrite <- H in H5; inv H5. rewrite Z.sub_simpl_r in H2, H6.
         destruct v1; inv H3; inv H7. simpl in *.

       - inv H5. rewrite Z.sub_simpl_r in H, H6. congruence. 

Print Mem.mem_inj.
mi_memval
       split; intros P.
       - destruct (PINV23 P); [ clear PINV23 | contradiction].
         specialize (Mem.perm_inject _ _ _ _ _ _ (z-d2) k p AI23' Minj23'). 
         rewrite Z.sub_simpl_r; intros X; apply X; clear X.
         apply U2; trivial. 
       - destruct (PINV23' P); clear PINV23' PINV23. 
         * specialize (Mem.perm_inject _ _ _ _ _ _ (z-d2) k p AI23 Minj23). 
           rewrite Z.sub_simpl_r; intros X; apply X; clear X.
           apply U2; trivial.
         * elim H; clear H. apply U2; trivial. 
       - specialize (Mem.perm_inject _ _ _ _ _ _ (z-d2) k p AI23 Minj23).
         rewrite Z.sub_simpl_r; intros X; apply X; clear X.
         destruct (PINV23' P); clear PINV23'. 
         apply U2; trivial. apply Mem.perm_valid_block in Perm2; trivial.
         elim H; clear H. apply U2; trivial. apply Mem.perm_valid_block in Perm2; trivial.
 admit. contradiction. Print mem_forward. Search Z.sub Z.add.  Print mem_forward.
Print Mem.inject'.

  Search mem_forward corestep_star. Ple. }
   { right. exists b1, (d1+d2).
     assert (Fb1: frgnBlocksSrc mu12 b1 = true) by apply (foreign_DomRng _ WD12 _ _ _ FRG12).
     rewrite Fb1. split; [| rewrite Z.add_comm, Z.sub_add_distr; trivial].
     apply foreign_in_extern in FRG12. apply foreign_in_extern in FRG23.
     eapply compose_meminjI_Some; eassumption. }
+ admit. (*return case similar*)
+ simpl in *. (*chenge DIV case in UNCH to FAlse?*) 
 Search Z.sub Z.add. minus Z.plus. compose_meminj Some.  intros X. rewrite X.
Search foreign_of extBlocksTgt. 
   right. left; trivial.
   right.
   assert (VB2 := Mem.perm_valid_block _ _ _ _ _ Perm2).
   destruct (UNCH2 _ (z-d2) VB2) as [U2 | [ LT2 | [b1 [d1 [FRG12 Perm1]]]]].
   right. left; trivial.
    
Admitted. (*
 - clear X12 X23. simpl; intros. (* constructor; intros.
   { inv STEP3. apply corestep_star_fwd in H2. apply mem_forward_nextblock in H2; trivial. }
   { destruct H0 as [X Y]; simpl in X, Y. inv H.
     eapply UNCH3; trivial. admit.
     split; trivial. intros.
Search mem_forward Ple. apply H2. STEP3. Search corestep_star. Mem.unchanged_on. unfold Mem.unchanged_on. red. simpl in UNCH2, UNCH3. clear X12 X23 INV' STEP1 STEP2 STEP3.*)
   exploit UNCH2; clear UNCH2.
     eapply mem_unchanged_on_sub; eauto.
   intros U2; clear H.
   exploit UNCH3; clear UNCH3.
   { eapply Mem.unchanged_on_implies. eassumption. 
     (* eapply mem_unchanged_on_sub; eauto.*)
     intros; clear U2. unfold extern_out_of_reach. unfold vis in H.
     apply orb_false_iff in H; destruct H.
     destruct INV as [INVa [INVb [INVc INVd]]]; rewrite INVa.
     split; [trivial | intros bb d Hb].
     remember (frgnBlocksSrc mu12 bb) as fb; symmetry in Heqfb.
     destruct fb; [ | right; trivial].
     destruct (frgnSrcAx _ WD12 _ Heqfb) as [b' [d' [E FRGN]]].
     rewrite E in Hb; inv Hb. apply INVd in FRGN; congruence. }
   simpl. simpl in *. Check Mem.perm.
forall b2 z (Eb2: extBlocksTgt m2 b2),
    Mem.unchanged_on (fun b' z' => (b,z)=(b'z')) m2 m2') \/
    (exists b1 d, extern_of mu b1 - Some(b2,d) /\ Mem.perm m1 b (z-d) Max Nonempty).

eq_block b b' 
   

clear U2; intros. eapply Mem.unchanged_on_implies. eassumption. 
     intros b3 d E vb. red; red in E; simpl in E; destruct E; split; [trivial | intros b2 delta E2].
     destruct (extern_DomRng _ WD23 _ _ _ E2) as [eSrc2 eTgt3].
     remember (frgnBlocksSrc mu23 b2) as frg; symmetry in Heqfrg.
     destruct frg; [left; intros N | right; trivial].
     destruct (mudec mu12 m1 m2 WD12 (match_validblocks _ _ _ _ _ _ _ _ _ _ _ MS12) b2).
     { destruct e as [b1 [d1 [vb1 MAP]]].
       destruct (joinD_Some _ _ _ _ _ MAP) as [E1 | [E1 Loc1]].
       + admit. (* destruct (H1 b1 (d1+delta)). eapply compose_meminjI_Some; eassumption. eauto.*)
       + assert (X: extBlocksTgt mu12 b2 = false). eapply local_locBlocks; eassumption.
         destruct INV as [INVa [INVb [INVc INVd]]]; rewrite INVb in X; congruence. }
     { 
 ; rewrite INVa.
         SearchAbout local_of locBlocksTgt. compose_meminj Some.
SearchAbout join. extern_of SM_wd extBlocksSrc.
       destruct (H1 b1
       unfold extern_out_of_reach. unfold vis in H.
      tradiction.  Search frgnBlocksSrc frgnBlocksTgt.
     remember (extBlocksSrc mu23 b) as eb; symmetry in Heqeb.
     destruct eb. Focus 2.
Search extBlocksSrc Mem.valid_block. Mem.unchanged_on Mem.valid_block.
   intros U2; clear H.

 clear - MCC12.
Search replace_locals frgnBlocksSrc. in MCC12.
Search replace_locals vis. REACH_closed.

  3: subst; rewrite compose_sm_exportedSrc; trivial.
  2: 
  
        rewrite compose_sm_exportedTgt; trivial. 

Focus 4. { subst nu. unfold replace_locals. simpl. f_equal. 
           + subst. rewrite compose_sm_exportedSrc; trivial.
           + subst. rewrite compose_sm_exportedTgt; trivial. }
Unfocus.
2: eapply compose_sm_wd; trivial.
2: rewrite compose_sm_as_inj; trivial; eapply Mem.inject_compose; eassumption.
Focus 2. subst. specialize (replace_locals_wd_AtExternal (compose_sm mu12' mu23') vals1 vals3 m1' m3').
         rewrite compose_sm_exportedSrc; trivial. rewrite compose_sm_exportedTgt; trivial.
         intros HH. apply HH; trivial.
         change (locBlocksSrc (compose_sm mu12' mu23')) with (locBlocksSrc mu12').
         change (locBlocksTgt (compose_sm mu12' mu23')) with (locBlocksTgt mu23').
         Check replace_locals_wd_AtExternal.
Search compose_sm locBlocksSrc. simpl. rewrite compose_sm_locBlocksSrc; trivial.
Search SM_wd replace_locals. compose_sm.
simpl in *.  Search exportedSrc. vis compose_sm.
  subst nu; simpl.

  exists c2' m2'.

  assert (HNU: nu = compose_sm
                 (replace_locals mu12 (fun b : block => locBlocksSrc mu12' b && REACH m1' (exportedSrc mu12' vals1) b)
                                      (fun b : block => locBlocksTgt mu12' b && REACH m2' (exportedTgt mu12' vals2) b))
                 (replace_locals mu23 (fun b : block => locBlocksSrc mu23' b && REACH m2' (exportedSrc mu23' vals2) b)
                                      (fun b : block => locBlocksTgt mu23' b && REACH m3' (exportedTgt mu23' vals3) b))).
  { destruct INV as [GlueL [GlueE [GlueP GlueF]]]. 
              subst nu. unfold compose_sm; simpl. f_equal. 
              rewrite replace_locals_locBlocksSrc. trivial.
              rewrite replace_locals_locBlocksTgt. trivial.
              subst pubSrc'. rewrite replace_locals_pubBlocksSrc. trivial. 
              subst pubTgt'. rewrite replace_locals_pubBlocksTgt. trivial.
              do 2 rewrite replace_locals_local. trivial.
              rewrite replace_locals_extBlocksSrc. trivial.
              rewrite replace_locals_extBlocksTgt. trivial.
              rewrite replace_locals_frgnBlocksSrc. trivial.
              rewrite replace_locals_frgnBlocksTgt. trivial. }
  
do 2 rewrite replace_locals_extern. trivial.
 . PT). Search exportedSrc compose_sm.
  split. admit.
  eapply inject_shared_replace_locals. 
Focus 4. simpl in 4: eassumption.
Search Mem.inject shared_of.
  { exists c2', m2', mu12', mu23'. unfold muINV.
    split; trivial.
    split. { clear X12 X23. subst. unfold compose_sm; simpl.
             f_equal. intuition.             -

 rewrite H4, H7.

 simpl.
Search locBlocksTgt restrict_sm. intern. _incr frgnBlocksTgt.
               simpl in LOCALLOC12. simpl in LOCALLOC23.
               destruct mu12; destruct mu12'; destruct mu23; destruct mu23'; simpl in *.
               destruct LOCALLOC12 as [? [QQ [? ?]]]; rewrite QQ.
               destruct LOCALLOC23 as [WW [? [? ?]]]; rewrite WW.
               red in INV; simpl in INV; intuition; subst; trivial.
             intuition. red in LOCALLOC12; simpl in *.
             destruct INC12; simpl in *. destruct  rewrite H. intuition. clear.
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
*)
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

