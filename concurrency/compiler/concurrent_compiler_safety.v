(* Concurrent Compiler Correcntess *)

(** Prove a simulation between the Clight concurrent semantics and 
    the x86 concurrent semantics.
*)

Require Import VST.concurrency.common.HybridMachineSig.
Require Import VST.concurrency.compiler.HybridMachine_simulation.
Require Import VST.concurrency.compiler.concurrent_compiler_simulation.


Section ConcurrentCopmpilerSafety.
  Import HybridMachineSig HybridCoarseMachine.

  Context {resources: Resources}
          {SemSource SemTarget: Semantics}
          {SourceThreadPool : @ThreadPool.ThreadPool _ SemSource}
          {TargetThreadPool : @ThreadPool.ThreadPool _ SemTarget}
          {SourceMachineSig: @MachineSig _ _ SourceThreadPool}
          {TargetMachineSig: @MachineSig _ _ TargetThreadPool}.
  
  Definition SourceHybridMachine:=
    @HybridCoarseMachine resources SemSource SourceThreadPool SourceMachineSig.
  
  Definition TargetHybridMachine:=
    @HybridCoarseMachine resources SemTarget TargetThreadPool TargetMachineSig.
  
  Lemma concurrent_simulation_safety_preservation:
    forall U res,
      HybridMachine_simulation
        _ _ _ _ _ _ _
        (ConcurMachineSemantics(HybridMachine:=SourceHybridMachine) U res)
        (ConcurMachineSemantics(HybridMachine:=TargetHybridMachine) U res) ->
      forall SourceMachineState m,
      (forall n, HybridCoarseMachine.csafe SourceMachineState n) 
  .
      
End ConcurrentCopmpilerSafety.