(* Clight Safety*)

(**
   Prove that csafety in Clight_new implies safety in Clight. 
*)
Require Import VST.concurrency.common.ClightSemantincsForMachines.
Require Import VST.concurrency.common.ClightMachine.
Require Import VST.concurrency.juicy.semax_to_juicy_machine.


Import HybridMachineSig.
Import HybridMachine.

Section Clight_safety_equivalence.
Context (CPROOF : semax_to_juicy_machine.CSL_proof).
Definition prog:= CPROOF.(CSL_prog).
Definition ge:= Clight.globalenv prog.
Definition init_mem:= proj1_sig (init_mem CPROOF).

(*We should be able to construct a Clight.state from the proof. *)
Axiom initial_Clight_state: CSL_proof -> Clight.state.
(*...And we should be able to constructe an intial state from the Clight_new and mem.*)
Axiom new2Clight_state: Clight_new.corestate -> Memory.mem -> Clight.state.
(*The two constructions commute.*)
Axiom initial_Clight_state_correct:
  new2Clight_state
    (initial_corestate CPROOF)
    init_mem = initial_Clight_state CPROOF.

Lemma Clight_new_Clight_safety:
  forall clight_new_state,
  (forall sch n,
    HybridMachineSig.HybridCoarseMachine.csafe
      (Sem := Clight_newSem ge)
      (ThreadPool:= threadPool.OrdinalPool.OrdinalThreadPool(Sem:=Clight_newSem ge))
      (machineSig:= HybridMachine.DryHybridMachine.DryHybridMachineSig)
      (sch, nil,
       DryHybridMachine.initial_machine
         (Sem := Clight_newSem ge)
         (permissions.getCurPerm init_mem)
        clight_new_state) init_mem n) ->
  forall sch n,
    HybridMachineSig.HybridCoarseMachine.csafe
      (Sem := ClightSem ge)
      (ThreadPool:= threadPool.OrdinalPool.OrdinalThreadPool(Sem:=ClightSem ge))
      (machineSig:= HybridMachine.DryHybridMachine.DryHybridMachineSig)
      (sch, nil, (DryHybridMachine.initial_machine
         (Sem := ClightSem ge)
         (permissions.getCurPerm init_mem)
         (new2Clight_state clight_new_state init_mem))) init_mem n.
Admitted.

(*

Theorem Clight_initial_safe (sch : HybridMachineSig.schedule) (n : nat) :
    HybridMachineSig.HybridCoarseMachine.csafe
      (Sem := ClightSem ge)
      (ThreadPool:= threadPool.OrdinalPool.OrdinalThreadPool(Sem:=ClightSem ge))
      (machineSig:= HybridMachine.DryHybridMachine.DryHybridMachineSig)
      (sch, nil,
       DryHybridMachine.initial_machine(Sem := ClightSem ge)
                                       (permissions.getCurPerm init_mem)
        (initial_Clight_state CPROOF)) init_mem n.
  Proof.

 *)



End Clight_safety_equivalence.