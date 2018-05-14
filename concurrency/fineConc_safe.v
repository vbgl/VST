(** * Safety of the FineConc Machine (generic)*)

Require Import compcert.lib.Axioms.

Require Import VST.concurrency.sepcomp. Import SepComp.
Require Import VST.sepcomp.semantics_lemmas.

Require Import VST.concurrency.pos.


From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.

(*NOTE: because of redefinition of [val], these imports must appear
  after Ssreflect eqtype.*)
Require Import compcert.common.AST.     (*for typ*)
Require Import compcert.common.Values. (*for val*)
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Events.
Require Import compcert.lib.Integers.

Require Import Coq.ZArith.ZArith.

Require Import VST.concurrency.threadPool.
Require Import VST.concurrency.dry_machine_lemmas.
Require Import VST.concurrency.dry_machine_step_lemmas.
Require Import VST.concurrency.threads_lemmas.
Require Import VST.concurrency.permissions.
Require Import VST.concurrency.HybridMachineSig.
Require Import VST.concurrency.mem_obs_eq.
Require Import VST.concurrency.compcert_threads_lemmas.
Require Import VST.concurrency.dry_context.
Require Import VST.concurrency.tactics.
Require Import Coqlib.
Require Import VST.msl.Coqlib2.

Set Bullet Behavior "None".
Set Bullet Behavior "Strict Subproofs".

Module FineConcInitial.

  Import Renamings MemObsEq ValObsEq ValueWD MemoryWD
         AsmContext CoreInjections event_semantics.

  Section FineConcInitial.

    Context {Sem : Semantics}
            {CI: CoreInj}.

  Variable init_mem : option Memory.Mem.mem.

  (** The initial memory is well-defined*)
  Parameter init_mem_wd:
    forall m, init_mem = Some m -> valid_mem m.

  (** The initial core is well-defined*)
  Parameter init_core_wd:
    forall c v args m (ARGS:valid_val_list (id_ren m) args),
      init_mem = Some m ->
      initial_core semSem 0 m c v args ->
      core_wd (id_ren m) c.

  (** The initial global env is well-defined*)
  Parameter the_ge_wd:
    forall m,
      init_mem = Some m ->
      ge_wd (id_ren m) the_ge.

End FineConcInitial.

End FineConcInitial.

(** ** Safety for FineConc (interleaving) semantics *)
Module FineConcSafe.

  Import ThreadPool AsmContext ThreadPoolWF HybridMachine DryHybridMachine HybridMachineSig.
  Import Renamings MemObsEq ValObsEq ValueWD CoreInjections FineConcInitial.
  Import StepType InternalSteps StepLemmas.

  Import MemoryWD ThreadPoolInjections event_semantics.

  Section FineConcSafe.

    Context {Sem : Semantics}
            {semAx: CoreLanguage.SemAxioms}
            {CI : CoreInj}.

  Variable init_mem : option Memory.Mem.mem.

  (** Excluded middle is required, but can be easily lifted*)
  Variable em : ClassicalFacts.excluded_middle.

  (* Is this the right instance? *)
  Existing Instance DryHybridMachine.dryResources.
  Existing Instance DryHybridMachine.DryHybridMachineSig.
  Existing Instance OrdinalPool.OrdinalThreadPool.
  Existing Instance dryFineMach.
  Existing Instance FineDilMem.
  Existing Instance dryCoarseMach.
  Existing Instance HybridFineMachine.scheduler.
  Existing Instance HybridCoarseMachine.scheduler.
  Existing Instance FineDilMem.
  Existing Instance HybridCoarseMachine.DilMem.

  Lemma init_tp_wd:
    forall v args m tp (ARGS:valid_val_list (id_ren m) args),
      init_mem = Some m ->
      @init_mach DryHybridMachine.dryResources _ _ _ (init_perm init_mem) m tp v args ->
      tp_wd (id_ren m) tp.
  Proof.
    intros.
    intros i cnti.
    simpl in H0.
    unfold DryHybridMachine.init_mach in H0.
    destruct H0 as [c [Hinit_core Hinit_perm]].
    unfold init_perm in Hinit_perm.
    rewrite H in Hinit_perm; subst.
    unfold ctl_wd.
    assert (Hget: getThreadC cnti = Krun c)
      by (unfold getThreadC, OrdinalPool.getThreadC;
          reflexivity).
    rewrite Hget.
    eapply init_core_wd;
      now eauto.
  Qed.

  (** Assuming safety of cooperative VST.concurrency*)
  Section Safety.

    Variables (f : val) (arg : list val) (initU : seq.seq nat).

    Variable init_coarse_safe:
      forall  U tpc mem sched n,
        init_mem = Some mem ->
        tpc_init initU init_mem mem (U, [::], tpc) f arg ->
        HybridCoarseMachine.csafe (sched,[::],tpc) mem n.

  (** If the initial state is defined then the initial memory was also defined*)
  Lemma tpc_init_mem_defined:
    forall U tpc m,
      tpc_init initU init_mem m (U, [::], tpc) f arg ->
      exists m, init_mem = Some m.
  Proof.
    unfold tpc_init. simpl.
    unfold HybridMachine.DryHybridMachine.init_mach. intros.
    destruct H as [? [Hinit Hinit_perm]].
    destruct init_perm eqn:?.
    unfold init_perm in *.
    destruct init_mem; try discriminate.
    eexists; reflexivity.
    destruct Hinit_perm;
      now exfalso.
  Qed.

  (** [init_mach] and [init_mem] are related by [mem_compatible]*)
  Lemma init_compatible:
    forall tp m,
      init_mem = Some m ->
      @init_mach DryHybridMachine.dryResources _ _ _ (init_perm init_mem) m tp f arg ->
      mem_compatible tp m.
  Proof.
    intros.
    destruct init_perm as [pmap|] eqn:Hinit_perm;
      [| eapply init_mach_none in H0; now exfalso].
    unfold init_perm in Hinit_perm.
    rewrite H in Hinit_perm.
    inversion Hinit_perm; subst.
    constructor.
    - intros j cntj.
      pose proof (init_thread H0 cntj); subst.
      erewrite getThreadR_init by eauto.
      simpl.
      split; [intros ? ?; now apply getCur_Max |now apply empty_LT].
    - intros.
      erewrite init_lockRes_empty in H by eauto.
      discriminate.
    - intros.
      erewrite init_lockRes_empty in H by eauto.
      discriminate.
  Qed.

  (** Simulation relation with id renaming for initial memory*)
  Lemma init_mem_obs_eq :
    forall m tp i (cnti : containsThread tp i)
      (Hcomp: mem_compatible tp m)
      (HcompF: mem_compatible tp (@diluteMem FineDilMem m)),
      init_mem = Some m ->
      @init_mach DryHybridMachine.dryResources _ _ _ (init_perm init_mem) m tp f arg ->
      mem_obs_eq (id_ren m) (restrPermMap (compat_th _ _ Hcomp cnti).1)
                 (restrPermMap (HcompF _ cnti).1) /\
      mem_obs_eq (id_ren m) (restrPermMap (Hcomp _ cnti).2)
                 (restrPermMap (HcompF _ cnti).2).
  Proof.
    intros.
    pose proof (mem_obs_eq_id (init_mem_wd H)) as Hobs_eq_id.
    unfold init_mach in H0. simpl in H0.
    unfold DryHybridMachine.init_mach in H0.
    destruct H0 as [c [Hinit Hinit_perm]].
    unfold init_perm in Hinit_perm.
    rewrite H in Hinit_perm.
    subst tp.
    destruct Hobs_eq_id.
    split.
    - constructor.
      + constructor;
          destruct weak_obs_eq0; eauto.
        intros.
        do 2 rewrite restrPermMap_Cur.
        simpl.
        apply id_ren_correct in Hrenaming. subst.
        apply po_refl.
      + constructor.
        intros.
        apply id_ren_correct in Hrenaming.
        subst.
        do 2 rewrite restrPermMap_Cur.
        reflexivity.
        intros.
        apply id_ren_correct in Hrenaming. subst b2.
        eapply memval_obs_eq_id.
        apply Mem.perm_valid_block in Hperm.
        simpl.
        pose proof (init_mem_wd H Hperm ofs ltac:(reflexivity)).
        destruct (ZMap.get ofs (Mem.mem_contents m) # b1); simpl; auto.
        rewrite <- wd_val_valid; eauto.
        apply id_ren_domain.
        apply id_ren_correct.
    - constructor.
      + constructor;
          destruct weak_obs_eq0; eauto.
        intros.
        do 2 rewrite restrPermMap_Cur.
        simpl.
        rewrite! empty_map_spec.
        now apply po_refl.
      + constructor.
        intros.
        do 2 rewrite restrPermMap_Cur.
        simpl.
        rewrite! empty_map_spec.
        reflexivity.
        intros.
        unfold Mem.perm in Hperm.
        pose proof (restrPermMap_Cur (Hcomp i cnti).2 b1 ofs).
        unfold permission_at in H0.
        rewrite H0 in Hperm.
        simpl in Hperm.
        rewrite empty_map_spec in Hperm.
        simpl in Hperm.
        now exfalso.
  Qed.

  (** The [strong_tsim] relation is reflexive under the identity renaming*)
  Lemma strong_tsim_refl:
    forall tp m i (cnti: containsThread tp i)
      (Hcomp: mem_compatible tp m)
      (HcompF: mem_compatible tp (@diluteMem FineDilMem m))
      (ARGS:valid_val_list (id_ren m) arg),
      init_mem = Some m ->
      @init_mach DryHybridMachine.dryResources _ _ _ (init_perm init_mem) m tp f arg ->
      SimDefs.strong_tsim (id_ren m) cnti cnti Hcomp HcompF.
  Proof.
    intros.
    destruct (init_mem_obs_eq cnti Hcomp HcompF H H0).
    constructor; eauto.
    eapply ctl_inj_id; eauto.
    apply (init_tp_wd ARGS H H0).
    now apply id_ren_correct.
  Qed.

  Lemma setMaxPerm_inv:
    forall m, SimDefs.max_inv (@diluteMem FineDilMem m).
  Proof.
    intros.
    unfold diluteMem, SimDefs.max_inv, Mem.valid_block, permission_at.
    simpl.
    intros b ofs H.
    simpl in H.
    apply setMaxPerm_MaxV with (ofs := ofs) in H.
    unfold permission_at in H.
    now auto.
  Qed.

  Lemma init_core_det:
    forall h m f arg c c',
      initial_core semSem h m c f arg ->
      initial_core semSem h m c' f arg ->
      c = c'.
  Proof.
  Admitted.

  (** Establishing the simulation relation for the initial state*)
  Lemma init_sim:
    forall U U' tpc tpf m n (ARG:valid_val_list (id_ren m) arg),
      tpc_init initU init_mem m (U, [::], tpc) f arg ->
      tpc_init initU init_mem m (U', [::], tpf) f arg ->
      init_mem = Some m ->
      SimDefs.sim tpc [::] m tpf [::] (@diluteMem FineDilMem m) nil (id_ren m) (id_ren m) (fun i cnti => id_ren m) n.
  Proof.
    intros.    
    unfold tpc_init, tpf_init in *. simpl in *.
    destruct H as [? HinitC].
    destruct H0 as [? HinitF].
    assert (HmemComp := init_compatible H1 HinitC).
    assert (HmemCompF0 := init_compatible H1 HinitF).
    pose proof HinitC as HinitC'.
    unfold DryHybridMachine.init_mach in HinitC, HinitF.
    destruct HinitC as [cc [HinitC Hinit_permC]].
    destruct HinitF as [cf [HinitF Hinit_permF]].
    unfold init_perm in *.
    rewrite H1 in Hinit_permF Hinit_permC.
    assert (HmemCompF: mem_compatible tpf (@diluteMem FineDilMem m))
      by (eapply mem_compatible_setMaxPerm; eauto).
    subst tpf tpc U U'.
    assert (cc = cf)
      by (eapply init_core_det; now eauto).
    subst cf.
    eapply SimDefs.Build_sim with (mem_compc := HmemComp) (mem_compf := HmemCompF).
    - intros; split; auto.
    - simpl. rewrite addn0.
      intros.
      eapply init_coarse_safe with (n := n); eauto.
    - intros i cnti cnti'.
      pose proof (strong_tsim_refl cnti HmemComp HmemCompF ARG H1 HinitC').
      Tactics.pf_cleanup.
      destruct H. destruct obs_eq_data, obs_eq_locks.
      constructor;
        now eauto.
    - intros; by congruence.
    - intros.
      exists (@mkPool dryResources _ _  (Krun cc) ((getCurPerm m, empty_map)#1, empty_map)), m.
      split; eauto with renamings.
      split; eauto.
      split; first by constructor.
      split.
      intros; Tactics.pf_cleanup.
      eapply strong_tsim_refl; eauto.
      pose proof (init_thread HinitC' pff); subst tid.
      repeat (split; intros); try congruence.
      + rewrite H1 in HinitC'.
        erewrite getThreadR_init by eauto.
        simpl.
        pose proof (strong_tsim_refl pfc HmemComp HmemCompF ARG  H1).
        rewrite H1 in H0. simpl in H0.
        specialize (H0 HinitC').
        Tactics.pf_cleanup.
        destruct H0. destruct obs_eq_data.
        destruct weak_obs_eq0.
        destruct (valid_block_dec m b2).
        * pose proof (domain_valid0 _ v) as Hmapped.
          destruct Hmapped as [b' Hid].
          pose proof (id_ren_correct _ _ Hid); subst.
          exfalso. apply H.
          eexists; eauto.
        * apply Mem.nextblock_noaccess with (k := Cur) (ofs := ofs) in n0.
          rewrite getCurPerm_correct.
          unfold permission_at.
          assumption.
      + erewrite getThreadR_init
          by ( unfold init_perm in HinitC';
               rewrite H1 in HinitC';
               eauto).
        simpl.
        now apply empty_map_spec.
    - unfold DryHybridMachine.init_mach in *.
      rewrite H1 in HinitC'.
      destruct HinitC' as [c' [HinitC' Heq]].
      split.
      + intros.
        exfalso.
        unfold initial_machine, lockRes in *. simpl in *.
        unfold OrdinalPool.mkPool, OrdinalPool.lockRes in *.
        simpl in Hl1, Hl2.
        erewrite OrdinalPool.find_empty in Hl1, Hl2.
        discriminate.
      + split.
        * intros.
          unfold lockRes, initial_machine in H.
          unfold OrdinalPool.mkPool, OrdinalPool.lockRes in *.
          simpl in H.
          now exfalso.
        * intros.
          apply id_ren_correct in H; subst.
          split; auto.
    - intros.
      unfold DryHybridMachine.init_mach in HinitC'.
      rewrite H1 in HinitC'.
      destruct HinitC' as [c' [HinitC' Heq]].
      unfold initial_machine, lockRes in *. simpl in *.
      unfold OrdinalPool.mkPool, OrdinalPool.lockRes in *.
      simpl in H.
      erewrite OrdinalPool.find_empty in H.
      discriminate.
    - eapply ThreadPoolWF.initial_invariant;
        now eauto.
    - apply setMaxPerm_inv; auto.
    - apply (@init_mem_wd _ _ H1); eauto.
    - eapply init_tp_wd; eauto.
    - eapply the_ge_wd; eauto.
    - split; eauto with renamings.
      apply id_ren_correct.
    - simpl. tauto.
  Qed.

  (** Proof of safety of the FineConc machine*)

  Notation fsafe := (@HybridFineMachine.fsafe _ _ _ _ FineDilMem).

  (** If a thread has reached an external then it cannot be in the
  list that denotes the delta of execution between the two machines *)
  Lemma at_external_not_in_xs:
    forall tpc trc mc tpf trf mf xs f fg fp i n
      (Hsim: SimDefs.sim tpc trc mc tpf trf mf xs f fg fp n)
      (pffi: containsThread tpf i),
      let mrestr := restrPermMap (compat_th _ _ (SimDefs.mem_compf Hsim) pffi).1 in
      forall (Hexternal: getStepType pffi mrestr Concurrent),
        ~ List.In i xs.
  Proof.
    intros; intro Hin.
    destruct Hsim.
    assert (pfci: containsThread tpc i)
      by (eapply numThreads; eauto).
    pose proof (simStrong _ pfci pffi) as HsimStrongi.
    destruct HsimStrongi as (tpc' & mc' & Hincr & _ & Hexec & Htsim & _).
    assert (pfci' : containsThread tpc' i)
      by (eapply InternalSteps.containsThread_internal_execution; eauto).
    assert (HmemCompC': mem_compatible tpc' mc')
      by (eapply InternalSteps.internal_execution_compatible with (tp := tpc) (m := mc);
          eauto; eapply Hexec).
    specialize (Htsim pfci' HmemCompC').
    destruct Htsim.
    clear - Hexec code_eq Hexternal Hin HmemCompC' obs_eq_data Hincr semAx.
    unfold getStepType in Hexternal.
    pose proof Hexec as Hexec'.
    eapply internal_execution_result_type with (cnti' := pfci') (Hcomp' := HmemCompC') in Hexec;
      eauto.
    unfold getStepType in Hexec.
    destruct fg_spec.
    erewrite SimProofs.ctlType_inj with (f:= fp i pfci) in Hexec; eauto.
    eapply ren_incr_trans; eauto.
    - erewrite <- restrPermMap_mem_valid.
      eapply SimProofs.internal_execution_wd; eauto.
      destruct (simWeak _ pfci pffi).
      erewrite restrPermMap_domain with (Hlt := (compat_th _ _ mem_compc pfci).1).
      eapply weak_obs_eq_domain_ren; now eauto.
      eapply ren_incr_domain_incr; now eauto.
  Qed.

  Lemma getStepType_cases:
    forall tp m i (cnti: containsThread tp i),
      getStepType cnti m Concurrent \/
      getStepType cnti m Internal \/
      getStepType cnti m Halted \/
      getStepType cnti m Suspend.
  Proof.
    intros.
    unfold getStepType, ctlType.
    destruct (getThreadC cnti); try auto.
    destruct (at_external semSem s m) eqn:?; try auto.
    destruct (em (exists i0, halted semSem s i0)) as [Hhalted | Hnothalted].
    right; right; left; now eauto.
    right; left; right; now eauto.
  Qed.
    
      
  (** Simulation between the two machines implies safety*)
  Lemma fine_safe:
    forall tpf trf tpc trc mf mc (g fg : memren) fp xs sched
      (Hsim: SimDefs.sim tpc trc mc tpf trf mf xs g fg fp (S (size sched))),
      @fsafe tpf mf sched (S (size sched)).
  Proof.
    intros.
    generalize dependent xs.
    generalize dependent mf.
    generalize dependent tpf.
    generalize dependent fp.
    generalize dependent tpc.
    generalize dependent trc.
    generalize dependent trf.
    generalize dependent mc.
    generalize dependent g.
    induction sched as [|i sched]; intros; simpl; auto.
    econstructor; simpl; eauto.
    destruct (OrdinalPool.containsThread_dec i tpf) as [cnti | invalid].
    - (** By case analysis on the step type *)
      pose proof (getStepType_cases (restrPermMap (compat_th _ _ (SimDefs.mem_compf Hsim) cnti).1)
                                  cnti) as Htype.
      destruct Htype as [Htype | [Htype | [Htype | Htype]]].
      + assert (~ List.In i xs)
          by (eapply at_external_not_in_xs; eauto).
        pose proof (@SimProofs.sim_external _ _ _ initU init_mem  em _ _ _ _ _ _ _ _ _ _ _ _ cnti H Hsim Htype) as Hsim'.
        destruct Hsim' as (tpc' & trc' & mc' & tpf' & mf' & f' & fp' & tr' & Hstep & Hsim'').
        specialize (IHsched _ _ _ _ _ _ _ _ _ Hsim'').
        specialize (Hstep sched).
        unfold corestep in Hstep.
        simpl in Hstep.
        eapply @HybridFineMachine.StepSafe with (dilMem := FineDilMem);
          eauto.
      + pose proof (@SimProofs.sim_internal _ _ _ initU init_mem _ _ _ _ _ _ _ _ _ _ _ _ cnti Hsim Htype) as
            (tpf' & m' & fp' & tr' & Hstep & Hsim').
        specialize (Hstep sched).
        specialize (IHsched _ _ _ _ _ _ _ _ _ Hsim').
        unfold corestep in Hstep.
        simpl in Hstep.
        econstructor 3; simpl; eauto.
      + pose proof (@SimProofs.sim_halted _ _ initU init_mem _ _ _ _ _  _ _ _  _ _  _  _ cnti Hsim Htype) as Hsim'.
        destruct Hsim' as (tr' & Hstep & Hsim'').
        specialize (IHsched _ _ _ _ _ _ _ _ _ Hsim'').
        specialize (Hstep sched).
        unfold corestep in Hstep.
        simpl in Hstep.
        econstructor 3;
          eauto.
      + pose proof (@SimProofs.sim_suspend _ _ _ initU init_mem em _ _ _ _ _ _ _  _ _ _ _ _ cnti Hsim Htype) as
            (tpc' & trc' & mc' & tpf' & mf' & f' & fp' & tr' & Hstep & Hsim').
        specialize (IHsched _ _ _ _ _ _ _ _ _ Hsim').
        specialize (Hstep sched).
        unfold corestep in Hstep.
        simpl in Hstep.
        econstructor 3; simpl;
          now eauto.
    -  pose proof (@SimProofs.sim_fail _ _  initU init_mem _ _ _ _  _  _ _  _ _ _ _ _ invalid Hsim) as
          (tr' & Hstep & Hsim').
       specialize (IHsched _ _ _ _ _ _ _ _ _ Hsim').
       specialize (Hstep sched).
       unfold corestep in Hstep.
       simpl in Hstep.
       econstructor 3; eauto.
       Unshelve. eapply [::].
  Qed.

  (** *** Safety preservation for the FineConc machine starting from the initial state*)
  Theorem init_fine_safe:
    forall tpf m
      (Hmem: init_mem = Some m)
      (Hinit: tpf_init initU init_mem m (initU, [::], tpf) f arg)
      (ARG: valid_val_list (id_ren m) arg),
    forall sched ,
      fsafe tpf (@diluteMem FineDilMem m) sched (size sched).+1.
  Proof.
    intros.
    assert (Hsim := init_sim (size sched).+1 ARG Hinit Hinit Hmem).
    eapply fine_safe;
      now eauto.
  Qed.

  End Safety.
End FineConcSafe.






