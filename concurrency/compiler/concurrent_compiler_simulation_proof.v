Require Import compcert.common.Globalenvs.

Require Import VST.concurrency.compiler.concurrent_compiler_simulation.
Require Import VST.concurrency.compiler.sequential_compiler_correct.


Module Concurrent_correctness (CC_correct: CompCert_correctness).

  
  Lemma ConcurrentCompilerCorrectness:
    forall (p:Clight.program) (tp:Asm.program),
      CC_correct.CompCert_compiler p = Some tp ->
      forall asm_genv_safety,
        ConcurrentCompilerCorrectness_specification
          (Clight.globalenv p) tp asm_genv_safety
          (Genv.init_mem (Ctypes.program_of_program p)) (Genv.init_mem tp)
  .
  Proof.
    unfold ConcurrentCompilerCorrectness_specification.
    intros.
    unfold ClightMachine.ClightMachine.DMS.ClightConcurSem, HybridMachineSig.HybridMachineSig.ConcurMachineSemantics, ClightMachine.ClightMachine.DMS.ClightMachine, HybridMachineSig.HybridMachineSig.HybridCoarseMachine.HybridCoarseMachine.
    eapply CC_correct.simpl_clight_semantic_preservation in H.
    econstructor.
    
  Admitted.
End Concurrent_correctness.