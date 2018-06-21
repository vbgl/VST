
Require Import VST.concurrency.compiler.concurrent_compiler_simulation.
Require Import VST.concurrency.compiler.concurrent_compiler_simulation_proof.
Require Import VST.concurrency.compiler.sequential_compiler_correct.
Require Import VST.concurrency.compiler.concurrent_compiler_safety.
Require Import VST.concurrency.compiler.concurrent_compiler_simulation_proof.
Require Import VST.concurrency.compiler.safety_equivalence.


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
  Lemma ConcurrentCompilerSafety:
    forall (p : Clight.program) (tp : Asm.program),
       CC_correct.CompCert_compiler p = Some tp ->
       forall asm_genv_safety : Asm_core.safe_genv (@the_ge tp),
         let SemSource:= (ClightSemantincsForMachines.ClightSem (Clight.globalenv p)) in
         let SemTarget:= @X86Sem tp asm_genv_safety in
    concurrent_simulation_safety_preservation_export 
      (SemSource:= SemSource)
      (SourceThreadPool:= threadPool.OrdinalPool.OrdinalThreadPool(Sem:=SemSource))
      (SourceMachineSig:= HybridMachine.DryHybridMachine.DryHybridMachineSig)
      (SemTarget :=  SemTarget)
      (TargetThreadPool:= threadPool.OrdinalPool.OrdinalThreadPool(Sem:=SemTarget))
      (TargetMachineSig:= HybridMachine.DryHybridMachine.DryHybridMachineSig)
      (Clight_init_state p)
      (Asm_init_state tp)
  .
    unfold concurrent_simulation_safety_preservation_export; intros.
    pose proof (ConcurrentCompilerCorrectness p tp H asm_genv_safety U) as HH.
    unfold ConcurrentCompilerCorrectness_specification in *.
    (*exploratory*)
    pose proof (HybridMachine_simulation.initial_setup HH) as INIT.
    simpl in INIT.
    unfold HybridMachineSig.HybridMachineSig.init_machine' in INIT.
    assert (tpool: @OrdinalPool.t HybridMachine.DryHybridMachine.dryResources
    (@DSem (Clight.globalenv p))) by admit.
    specialize (INIT (@the_ge tp)(Clight.globalenv p) init_thread init_mem_source
                     init_mem_source main args tpool
                     (Some (permissions.getCurPerm init_mem_source, permissions.empty_map))).
    simpl in *.
    unfold HybridMachine.DryHybridMachine.init_mach in *.
    simpl in *.
    match type of INIT with
      | ?A -> ?B => assert A
    end.
    admit.
    specialize (INIT H2).
    match type of INIT with
      | ?A -> ?B => assert A
    end.
    eexists.
    
    unfold HH.
    
    
    assert (HybridMachine_simulation.initial_source_thread
              HH init_mem_source init_thread main args).
    simpl.
    eapply HybridMachine_simulation.initial_setup in H0.
 
      (ConcurrentCompilerCorrectness_specification
            (Clight.globalenv p) tp asm_genv_safety).
    
  Admitted.
      
End Concurrent_Safety.
