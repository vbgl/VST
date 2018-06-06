
Require Import VST.concurrency.compiler.concurrent_compiler_simulation.
Require Import VST.concurrency.compiler.sequential_compiler_correct.
Require Import VST.concurrency.compiler.concurrent_compiler_safety.
Require Import VST.concurrency.compiler.concurrent_compiler_simulation_proof.


(*Clight Machine *)
Require Import VST.concurrency.common.DryMachineSource.
(*Asm Machine*)
Require Import VST.concurrency.common.x86_context.

Module Concurrent_Safety (CC_correct: CompCert_correctness).
  (*Import the Clight Hybrid Machine*)
  Import THE_DRY_MACHINE_SOURCE.
  Import DMS.
  (*Import the Asm X86 Hybrid Machine*)
  Import X86Context.
  
  Module ConcurCC_correct:= (Concurrent_correctness CC_correct).
  Import ConcurCC_correct.

  Parameter init_state_source:
    forall p,
    Clight.genv -> Memory.mem -> @semantics.semC (@DSem (Clight.globalenv p)) -> Values.val -> list Values.val -> Prop.
  
  Search semantics.Semantics.
  Lemma ConcurrentCompilerSafety:
    forall (p : Clight.program) (tp : Asm.program),
       CC_correct.CompCert_compiler p = Some tp ->
       forall asm_genv_safety : Asm_core.safe_genv (the_ge tp),
         let SemSource:= (ClightSemantincsForMachines.ClightSem (Clight.globalenv p)) in
         let SemTarget:= X86Sem tp asm_genv_safety in
    concurrent_simulation_safety_preservation_export 
      (SemSource:= SemSource)
      (SourceThreadPool:= threadPool.OrdinalPool.OrdinalThreadPool(Sem:=SemSource))
      (SourceMachineSig:= HybridMachine.DryHybridMachine.DryHybridMachineSig)
      (SemTarget :=  SemTarget)
      (TargetThreadPool:= threadPool.OrdinalPool.OrdinalThreadPool(Sem:=SemTarget))
      (TargetMachineSig:= HybridMachine.DryHybridMachine.DryHybridMachineSig)
      (init_state_source p)
  .
    unfold concurrent_simulation_safety_preservation; simpl; intros.
  Admitted.
      
End Concurrent_Safety.
