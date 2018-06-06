Require Import VST.concurrency.compiler.concurrent_compiler_simulation.
Require Import VST.concurrency.compiler.sequential_compiler_correct.


Module Concurrent_correctness (CC_correct: CompCert_correctness).
  
  Lemma ConcurrentCompilerCorrectness:
    forall (p:Clight.program) (tp:Asm.program),
      CC_correct.CompCert_compiler p = Some tp ->
      forall asm_genv_safety,
        ConcurrentCompilerCorrectness_specification (Clight.globalenv p) tp asm_genv_safety.
  Proof.
  Admitted.
End Concurrent_correctness.