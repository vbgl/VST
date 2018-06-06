(* Concurrent Compiler Correcntess *)

(** Prove a simulation between the Clight concurrent semantics and 
    the x86 concurrent semantics.
 *)

Require Import VST.concurrency.common.HybridMachineSig.
Require Import VST.concurrency.compiler.HybridMachine_simulation.
Require Import VST.concurrency.compiler.concurrent_compiler_simulation.

Set Implicit Arguments.

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
  
  Definition concurrent_simulation_safety_preservation 
    init_U
      (SIM: HybridMachine_simulation 
              (ConcurMachineSemantics(HybridMachine:=SourceHybridMachine) init_U)
              (ConcurMachineSemantics(HybridMachine:=TargetHybridMachine) init_U)):=
    forall U ge init_mem_source init_thread main args,
      match_initial_thread SIM ge init_mem_source init_thread main args ->
      let res:= permissions.getCurPerm init_mem_source in
      let init_tp_source:= ThreadPool.mkPool (Krun init_thread) (res,permissions.empty_map) in
      let init_MachState_source:= (U, nil, init_tp_source) in
      (forall n, HybridCoarseMachine.csafe init_MachState_source init_mem_source n) ->
      exists init_mem_target init_thread_target,
        let res_target:= permissions.getCurPerm init_mem_target in
        let init_tp_target:= ThreadPool.mkPool (Krun init_thread_target) (res_target,permissions.empty_map) in
        let init_MachState_target:= (U, nil, init_tp_target) in
        (forall n, HybridCoarseMachine.csafe init_MachState_target init_mem_target n).


  (* We define a simpler version that doesn't depend on SIM,
     then we reduce it to the previous version by showing:
     match_initial_thread SIM -> source_init_state
   *)
  Definition concurrent_simulation_safety_preservation_export
             (source_init_state:
                @G SemSource -> Memory.mem -> @semC SemSource -> Values.val -> list Values.val -> Prop)  :=
    forall U ge init_mem_source init_thread main args,
      source_init_state ge init_mem_source init_thread main args ->
      let res:= permissions.getCurPerm init_mem_source in
      let init_tp_source:= ThreadPool.mkPool
                             (Sem:=SemSource)
                             (Krun init_thread) (res,permissions.empty_map) in
      let init_MachState_source:= (U, nil, init_tp_source) in
      (forall n, HybridCoarseMachine.csafe
              (Sem:=SemSource)
              (ThreadPool:=SourceThreadPool)
              (machineSig:=SourceMachineSig)
              init_MachState_source init_mem_source n) ->
      exists init_mem_target init_thread_target,
        let res_target:= permissions.getCurPerm init_mem_target in
        let init_tp_target:= ThreadPool.mkPool
                               (Sem:=SemTarget) (Krun init_thread_target) (res_target,permissions.empty_map) in
        let init_MachState_target:= (U, nil, init_tp_target) in
        (forall n, HybridCoarseMachine.csafe
                (Sem:=SemTarget)
                (ThreadPool:=TargetThreadPool)
                (machineSig:=TargetMachineSig)
                init_MachState_target init_mem_target n).

  Lemma concur_safety_preserv_equiv:
    forall (source_init_state:
       @G SemSource -> Memory.mem -> @semC SemSource -> Values.val -> list Values.val -> Prop)
      init_U SIM,
      (forall ge init_mem_source init_thread main args,
        source_init_state ge init_mem_source init_thread main args ->
        match_initial_thread SIM ge init_mem_source init_thread main args) ->
    @concurrent_simulation_safety_preservation init_U SIM ->
    concurrent_simulation_safety_preservation_export source_init_state.
  Proof.
    intros ???? H ?; intros.
    eapply H; eauto.
  Qed.
    
End ConcurrentCopmpilerSafety.