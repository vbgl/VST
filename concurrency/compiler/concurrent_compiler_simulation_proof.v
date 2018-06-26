Require Import compcert.common.Globalenvs.

Require Import VST.concurrency.compiler.concurrent_compiler_simulation.
Require Import VST.concurrency.compiler.sequential_compiler_correct.


(*
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

  

  (* First construct the Clight machine and the two projections:
     - ClightMachineSem (i.e.  MachineSemantics) 
     - ClightConcurSem (i.e. ConcurMachineSemantics)
  *)
  
  Definition ClightMachine :=(HybridCoarseMachine.HybridCoarseMachine
                                 (machineSig := DryHybridMachine.DryHybridMachineSig)).
  Definition ClightMachineSem := (MachineSemantics(HybridMachine := ClightMachine)).
  Definition ClightConcurSem := (ConcurMachineSemantics(HybridMachine := ClightMachine)). 
  

  
  Lemma compile_one_thread:
    
    HybridMachine_simulation.HybridMachine_simulation
  
  
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