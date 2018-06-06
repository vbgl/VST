(* Concurrent Compiler Correcntess *)

(** Prove a simulation between the Clight concurrent semantics and 
    the x86 concurrent semantics.
*)

Require Import VST.concurrency.common.HybridMachineSig.
Require Import VST.concurrency.compiler.HybridMachine_simulation.
Require Import VST.concurrency.compiler.concurrent_compiler_simulation.


Section ConcurrentCopmpilerSafety.
  Import HybridMachineSig HybridCoarseMachine.

  (*This definitions are specialized to dry machines
    Why? to show that the initial res is defined by the initial mem
   *)
  Notation resources:= HybridMachine.DryHybridMachine.dryResources.
  Context {SemSource SemTarget: Semantics}
          {SourceThreadPool : @ThreadPool.ThreadPool _ SemSource}
          {TargetThreadPool : @ThreadPool.ThreadPool _ SemTarget}
          {SourceMachineSig: @MachineSig _ _ SourceThreadPool}
          {TargetMachineSig: @MachineSig _ _ TargetThreadPool}.
  
  Definition SourceHybridMachine:=
    @HybridCoarseMachine resources SemSource SourceThreadPool SourceMachineSig.
  
  Definition TargetHybridMachine:=
    @HybridCoarseMachine resources SemTarget TargetThreadPool TargetMachineSig.
  
  Definition concurrent_simulation_safety_preservation:=
    forall U
      (SIM: HybridMachine_simulation 
        (ConcurMachineSemantics(HybridMachine:=SourceHybridMachine) U)
        (ConcurMachineSemantics(HybridMachine:=TargetHybridMachine) U)),
      forall ge m init_thread main args,
        match_initial_thread SIM ge m init_thread main args ->
        let res:= permissions.getCurPerm m in
        let init_tp_source:= ThreadPool.mkPool (Krun init_thread) (res,permissions.empty_map) in
        let init_MachState_source:= (U, nil, init_tp_source) in
        (forall n, HybridCoarseMachine.csafe init_MachState_source m n) ->
        exists init_mem_target init_thread_target,
        let res_target:= permissions.getCurPerm init_mem_target in
        let init_tp_target:= ThreadPool.mkPool (Krun init_thread_target) (res_target,permissions.empty_map) in
        let init_MachState_target:= (U, nil, init_tp_target) in
        (forall n, HybridCoarseMachine.csafe init_MachState_target m n).

  
End ConcurrentCopmpilerSafety.