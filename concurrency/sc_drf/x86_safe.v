(** ** Erased X86 machine is safe*)

Require Import compcert.lib.Axioms.

Require Import VST.concurrency.common.sepcomp. Import SepComp.
Require Import VST.sepcomp.semantics_lemmas.
Require Import VST.concurrency.common.pos.

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
Require Import compcert.x86.Asm.

Require Import Coq.ZArith.ZArith.

Require Import VST.concurrency.common.threadPool.
Require Import VST.concurrency.common.threads_lemmas.
Require Import VST.concurrency.common.permissions.
Require Import VST.concurrency.common.dry_machine_lemmas.
Require Import VST.concurrency.common.HybridMachine.
Require Import VST.concurrency.common.erased_machine.
Require Import VST.concurrency.common.HybridMachineSig.
Require Import VST.concurrency.common.dry_context.
Require Import VST.concurrency.common.x86_context.
Require Import VST.concurrency.common.Asm_core.
Require Import VST.concurrency.sc_drf.x86_inj.
Require Import VST.concurrency.sc_drf.fineConc_safe.
Require Import VST.concurrency.sc_drf.SC_erasure.

Require Import Coqlib.
Require Import VST.msl.Coqlib2.

Module X86Safe.

  Import AsmContext SCErasure X86Context X86SEMAxioms HybridMachine
         HybridMachineSig HybridCoarseMachine HybridFineMachine
         FineConcSafe FineConcInitial.

  Section X86Safe.

    Context {U: seq.seq nat}
            {the_program: Asm.program}
            {Hsafe: Asm_core.safe_genv (@the_ge the_program)}.
    
    Instance X86Sem : Semantics := @X86Sem the_program Hsafe.
    Instance X86Axioms : CoreLanguage.SemAxioms := @X86Axioms U the_program Hsafe.
    Context {CE : @CoreErasure.CoreErasure X86Sem}. (*TODO: replace with instance *)
    Existing Instance X86Inj.X86Inj. 
    Context {FI : FineInit}. (* We don't really have an instance for that, it would require to prove that
                                the initial memory has no invalid pointers *)
    Variable em : ClassicalFacts.excluded_middle.
    

    Existing Instance dryCoarseMach.
    Existing Instance dryFineMach.
    Existing Instance bareMach.


    Lemma x86SC_safe:
      forall Main_ptr init_mem_target init_thread_target
        (Hinit_mem_defined: init_mem = Some init_mem_target),
        let init_perm_target := permissions.getCurPerm init_mem_target in
        let init_tpc_target := DryHybridMachine.initial_machine init_perm_target init_thread_target in
        let init_MachState_target := (U, nil, init_tpc_target) in
        forall
          (Hinit_state: tpc_init U init_mem init_mem_target init_MachState_target Main_ptr nil)
          (Hcsafe: forall n sched,
              csafe
                (ThreadPool:= threadPool.OrdinalPool.OrdinalThreadPool)
                (resources:= DryHybridMachine.dryResources)
                (Sem:= _)
                (machineSig:= HybridMachine.DryHybridMachine.DryHybridMachineSig)
                (sched, nil, init_tpc_target) (@diluteMem HybridCoarseMachine.DilMem init_mem_target) n),
          let init_tp_bare := ThreadPool.mkPool
                                (resources:=BareMachine.resources)
                                (Krun init_thread_target) tt  in
          forall n,
            fsafe
              (dilMem:= BareDilMem)
              (ThreadPool:=threadPool.OrdinalPool.OrdinalThreadPool
                             (resources:=erased_machine.BareMachine.resources)
                             (Sem:=_))
              (machineSig:= BareMachine.BareMachineSig)
              init_tp_bare (@diluteMem BareDilMem init_mem_target) U n.
    Proof.
      intros.
      (** Fine to Erased safety *)
      eapply init_fsafe_implies_scsafe; eauto.
      econstructor; eauto.
      simpl.
      unfold BareMachine.init_mach.
      inv Hinit_state.
      simpl in H0.
      unfold DryHybridMachine.init_mach in H0.
      destruct H0 as [c [Hinit_core ?]].
      exists c.
      split; eauto.
      assert (c = init_thread_target).
      { unfold initial_machine in init_tpc_target.
        unfold init_perm in H0.
        rewrite Hinit_mem_defined in H0.
        unfold init_tpc_target in H0.
        simpl in H0.
        unfold OrdinalPool.mkPool in H0.
        inv H0.
        eapply Eqdep.EqdepTheory.inj_pair2 in H2.
        clear -H2.
        assert (cnt: (0<1)%nat) by auto.
        pose proof (Ordinal cnt) as I1.
        assert (Heq: Krun init_thread_target = Krun c)
          by (eapply equal_f in H2; eauto).
        inv Heq.
        reflexivity.
      }
      subst.
      unfold init_tp_bare.
      reflexivity.
      (** Coarse to Fine safety *)
      eapply init_fine_safe; eauto.
      intros sched  tpc mem n0 Hinit_mem Htpc.
      rewrite Hinit_mem_defined in Hinit_mem. inv Hinit_mem.
      inversion Htpc; subst.
      simpl in Hcsafe.
      specialize (Hcsafe n0).
      unfold init_MachState_target, init_tpc_target in Hcsafe.
      simpl in Hcsafe.
      assert (tpc = OrdinalPool.mkPool (Krun init_thread_target) (init_perm_target, empty_map)).
      { simpl in H0.
        destruct H0 as [c0 [Hinit_core0 Hinit_pool0]].
        unfold init_perm in Hinit_pool0.
        rewrite Hinit_mem_defined in Hinit_pool0.
        subst.
        simpl.
        unfold init_perm_target.
        eapply f_equal2; try reflexivity.
        inv Hinit_state.
        inv H1.
        destruct H2 as [Hinit_core Hinit_tp].
        unfold init_perm in Hinit_tp.
        rewrite Hinit_mem_defined in Hinit_tp.
        unfold init_tpc_target in Hinit_tp. simpl in Hinit_tp.
        unfold OrdinalPool.mkPool in Hinit_tp.
        inv Hinit_tp.
        eapply Eqdep.EqdepTheory.inj_pair2 in H2.
        assert (cnt: (0<1)%nat) by auto.
        pose proof (Ordinal cnt) as I1.
        assert (Heq: Krun init_thread_target = Krun x)
          by (eapply equal_f in H2; eauto).
        inv Heq.
        apply f_equal.
        eapply initial_core_det;
          now eauto.
      }
      subst; now eauto.
      econstructor.
    Qed.

  End X86Safe.
End X86Safe.
               