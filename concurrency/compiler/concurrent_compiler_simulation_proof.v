Require Import compcert.common.Globalenvs.

Require Import VST.concurrency.compiler.concurrent_compiler_simulation.
Require Import VST.concurrency.compiler.sequential_compiler_correct.
Require Import VST.concurrency.compiler.CoreSemantics_sum.


(*Clight Machine *)
Require Import VST.concurrency.common.ClightMachine.
(*Asm Machine*)
Require Import VST.concurrency.common.x86_context.


(** *One thread simulation*)
Module OneThreadSimulation (CC_correct: CompCert_correctness).
  
  Import HybridMachineSig.

  Module DMS.
  Section DMS.

  Existing Instance OrdinalPool.OrdinalThreadPool.
  Context (Clight_g : Clight.genv).
  Definition CSem : Semantics := ClightSemantincsForMachines.ClightSem Clight_g.
  
  Import X86Context.

  (*Import the Asm Hybrid Machine*)
  Context (Asm_g : Clight.genv).
  Context (Asm_program: Asm.program).
  Context (Asm_genv_safe: Asm_core.safe_genv (@the_ge Asm_program)).

  
  Definition AsmSem : Semantics := @X86Sem Asm_program Asm_genv_safe.

  (** The hybrid semantics*)
  Definition HybridSem h : Semantics := CoreSem_Sum h CSem AsmSem.

  Existing Instance HybridMachine.DryHybridMachine.dryResources.
  Notation TP h := (threadPool.OrdinalPool.OrdinalThreadPool(Sem:=HybridSem h)).
  Existing Instance HybridMachine.DryHybridMachine.DryHybridMachineSig.

  Definition HybMachine h:=
    HybridMachineSig.HybridCoarseMachine.HybridCoarseMachine
      (ThreadPool:= TP h).

  Definition HybConcSem h:=
    HybridMachineSig.ConcurMachineSemantics(HybridMachine:=HybMachine h).

  Section CompileOneThread.
    
    Lemma compile_one_thread:
      forall n m,
        HybridMachine_simulation.HybridMachine_simulation
          (HybConcSem (Some n) m)
          (HybConcSem (Some (S n)) m).
    Proof.
      intros.
    Admitted.

  End CompileOneThread.

  
  Section CompileNThread.
  
  Lemma compile_n_threads:
      forall n m,
        HybridMachine_simulation.HybridMachine_simulation
          (HybConcSem (Some 0) m)
          (HybConcSem (Some n) m).
    Proof.
      intros.
    Admitted.

  End CompileNThread.

  
      
  
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
    apply CC_correct.simpl_clight_semantic_preservation in H.
    unfold ClightMachine.ClightMachine.DMS.ClightConcurSem, HybridMachineSig.HybridMachineSig.ConcurMachineSemantics, ClightMachine.ClightMachine.DMS.ClightMachine, HybridMachineSig.HybridMachineSig.HybridCoarseMachine.HybridCoarseMachine.
    econstructor.
*)


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
    apply CC_correct.simpl_clight_semantic_preservation in H.
    unfold ClightMachine.ClightMachine.DMS.ClightConcurSem, HybridMachineSig.HybridMachineSig.ConcurMachineSemantics, ClightMachine.ClightMachine.DMS.ClightMachine, HybridMachineSig.HybridMachineSig.HybridCoarseMachine.HybridCoarseMachine.
    econstructor.
    
  Admitted.
End Concurrent_correctness.