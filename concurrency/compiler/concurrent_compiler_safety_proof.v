
Require Import VST.concurrency.compiler.concurrent_compiler_simulation.
Require Import VST.concurrency.compiler.sequential_compiler_correct.
Require Import VST.concurrency.compiler.concurrent_compiler_safety.
Require Import VST.concurrency.compiler.concurrent_compiler_simulation_proof.


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
    Asm.entry_point (the_ge p).
  
  
  Parameter init_state_source'':
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
      (Clight_init_state p)
      (Asm_init_state tp)
  .
    unfold concurrent_simulation_safety_preservation; simpl; intros.
  Admitted.
      
End Concurrent_Safety.
