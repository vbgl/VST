
Require Import VST.concurrency.common.HybridMachineSig.
Import HybridMachineSig.

Require Import VST.concurrency.compiler.concurrent_compiler_simulation.
Require Import VST.concurrency.compiler.concurrent_compiler_simulation_proof.
Require Import VST.concurrency.compiler.sequential_compiler_correct.
Require Import VST.concurrency.compiler.concurrent_compiler_safety.
Require Import VST.concurrency.compiler.concurrent_compiler_simulation_proof.
Require Import VST.concurrency.compiler.safety_equivalence.
Require Import VST.concurrency.compiler.HybridMachine_simulation.


(*Clight Machine *)
Require Import VST.concurrency.common.ClightMachine.
(*Asm Machine*)
Require Import VST.concurrency.common.x86_context.

Module Concurrent_Safety (CC_correct: CompCert_correctness).
  (*Import the Clight Hybrid Machine*)
  Import ClightMachine.
  Import DMS.
  (*Import the Asm X86 Hybrid Machine*)
  Import X86Context.
  
  Module ConcurCC_correct:= (Concurrent_correctness CC_correct).
  Import ConcurCC_correct.

  Definition Clight_init_state (p: Clight.program):=
    Clight.entry_point (Clight.globalenv p).

    Definition Asm_init_state (p: Asm.program):=
    Asm.entry_point (@the_ge p).
  
    Search semantics.Semantics.


    
    Lemma explicit_safety_step:
      forall (p : Clight.program) (tp : Asm.program) (asm_genv_safety : Asm_core.safe_genv the_ge),
        let SemSource:= (ClightSemantincsForMachines.ClightSem (Clight.globalenv p)) in
         let SemTarget:= @X86Sem tp asm_genv_safety in
         forall (U : schedule) (m_s m_t : Memory.Mem.mem)
             (j : Values.Val.meminj) (c : Asm.state)
             (C_source : OrdinalPool.t(Sem:=SemSource))
             (C_target : OrdinalPool.t(Sem:=SemTarget)) tr
             (SIM : HybridMachine_simulation (ClightConcurSem U)
                                             (AsmConcurSem U)) (cd : index SIM),
           match_state SIM cd j C_source m_s C_target
                    m_t ->
        (forall U,
            explicit_safety
              HybridMachine.DryHybridMachine.dryResources
              SemSource
              (threadPool.OrdinalPool.OrdinalThreadPool(Sem:=SemSource))
              HybridMachine.DryHybridMachine.DryHybridMachineSig
              U tr C_source m_s) ->
        forall U,
            explicit_safety
              HybridMachine.DryHybridMachine.dryResources
              SemTarget
              (threadPool.OrdinalPool.OrdinalThreadPool(Sem:=SemTarget))
              HybridMachine.DryHybridMachine.DryHybridMachineSig
              U tr C_target m_t.
    Proof.
    Admitted.



    Lemma csafety_step:
      forall (p : Clight.program) (tp : Asm.program) (asm_genv_safety : Asm_core.safe_genv the_ge),
        let SemSource:= (ClightSemantincsForMachines.ClightSem (Clight.globalenv p)) in
         let SemTarget:= @X86Sem tp asm_genv_safety in
         forall (U : schedule) (init_mem_source' : Memory.Mem.mem)
             (j : Values.Val.meminj) (c : Asm.state)
             (C_source : OrdinalPool.t(Sem:=SemSource))
             (C_target : OrdinalPool.t) tr
             (SIM : HybridMachine_simulation (ClightConcurSem U)
                                             (AsmConcurSem U)) (cd : index SIM),
        match_state SIM cd j C_source init_mem_source' C_target
                    (Asm.get_mem c) ->
        (forall n : nat,
            HybridCoarseMachine.csafe(Sem:=SemSource)
                                     (resources:=HybridMachine.DryHybridMachine.dryResources)
                                     (ThreadPool:= threadPool.OrdinalPool.OrdinalThreadPool(Sem:=SemSource))
      (machineSig:= HybridMachine.DryHybridMachine.DryHybridMachineSig)
                                     (U, tr, C_source)
                                      init_mem_source' n) ->
        forall n : nat,
          HybridCoarseMachine.csafe (Sem:=SemTarget)
                                     (resources:=HybridMachine.DryHybridMachine.dryResources)
                                     (ThreadPool:= threadPool.OrdinalPool.OrdinalThreadPool(Sem:=SemTarget))
      (machineSig:= HybridMachine.DryHybridMachine.DryHybridMachineSig)
                                     (U, tr, C_target)
                                     (Asm.get_mem c) n.
    Proof.
      intros.
      eapply explicit_safety_csafe; eauto; intros.
      - admit. (*Initial scheudle is valid. *)
      - eapply explicit_safety_step in H; eauto.
        eapply csafe_explicit_safety; simpl.
        
        
    Admitted.


    
    Lemma ConcurrentCompilerSafety:
      forall (p : Clight.program) (tp : Asm.program),
        CC_correct.CompCert_compiler p = Some tp ->
        forall asm_genv_safety : Asm_core.safe_genv (@the_ge tp),
          let SemSource:= (ClightSemantincsForMachines.ClightSem (Clight.globalenv p)) in
          let SemTarget:= @X86Sem tp asm_genv_safety in
          concurrent_simulation_safety_preservation 
            (SemSource:= SemSource)
            (SourceThreadPool:= threadPool.OrdinalPool.OrdinalThreadPool(Sem:=SemSource))
            (SourceMachineSig:= HybridMachine.DryHybridMachine.DryHybridMachineSig)
            (SemTarget :=  SemTarget)
            (TargetThreadPool:= threadPool.OrdinalPool.OrdinalThreadPool(Sem:=SemTarget))
            (TargetMachineSig:= HybridMachine.DryHybridMachine.DryHybridMachineSig)
    .
      unfold concurrent_simulation_safety_preservation; intros.
      pose proof (ConcurrentCompilerCorrectness p tp H asm_genv_safety U) as SIM.

      (*Construct the initial state*)
      
      apply (HybridMachine_simulation.initial_setup SIM) in H0 as
          (j&cd&t_mach_state&t_mem&t_mem'&r2&INIT&?).
      assert(INIT':= INIT).
      destruct r2; try solve[inversion INIT'].
      destruct INIT' as (c&?&?).
      subst t_mach_state; simpl in *.
      do 3 eexists; split; eauto.
      destruct H2 as (H21 & H22); subst.
      clear INIT H21.

      (* Step preserves safety*)
      eapply safety_step; try eapply H0; eauto.
    Qed.
      
End Concurrent_Safety.
