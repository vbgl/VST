From mathcomp.ssreflect Require Import ssreflect seq ssrbool ssrfun.
Require Import compcert.common.Memory.
Require Import compcert.common.AST.     (*for typ*)
Require Import compcert.common.Values. (*for val*)
Require Import compcert.common.Globalenvs.
Require Import compcert.lib.Integers.
Require Import compcert.common.Values.

Require Import VST.msl.Axioms.
Require Import Coq.ZArith.ZArith.
Require Import VST.sepcomp.semantics.
Require Import VST.sepcomp.event_semantics.
Require Export VST.concurrency.common.semantics.
Require Export VST.concurrency.common.lksize.
Require Import VST.concurrency.common.threadPool. Export threadPool.

Require Import VST.concurrency.common.machine_semantics.
Require Import VST.concurrency.common.permissions.
Require Import VST.concurrency.common.bounded_maps.
Require Import VST.concurrency.common.addressFiniteMap.

Require Import VST.concurrency.common.scheduler.
Require Import Coq.Program.Program.

Require Import VST.concurrency.safety.

Require Import VST.concurrency.coinductive_safety.


Require Import VST.concurrency.common.HybridMachineSig.

Require Import VST.veric.res_predicates.

Require Import VST.concurrency.common.HybridMachine.

Require Import VST.concurrency.compiler.CoreSemantics_sum.

Require Import compcert.common.Smallstep.

Require Import VST.concurrency.common.machine_semantics_lemmas.


Section HybridSimulation. 

  (*
  Variable (Sems Semt : semantics.Semantics).
  Variable (hb1 hb2: option nat).
  (*Variable (Resources : Resources_rec).
  Variable (MatchCAsm: meminj -> corestate -> mem -> Asm_coop.state -> mem -> Prop).*)
  
  Definition HM1:=HybridMachine hb1 Sems Semt.
  Definition HM2:=HybridMachine hb2 Sems Semt.

  Notation Sem1:=(ConcurMachineSemantics HM1).
  Notation Sem2:=(ConcurMachineSemantics HM2).
  
  Notation C1:= (MachState HybridMachine.Resources
                          (Sem hb1 Sems Semt) (ThreadPool hb1 Sems Semt)).
  Notation C2:= (MachState HybridMachine.Resources
                          (Sem hb2 Sems Semt) (ThreadPool hb2 Sems Semt)).
  Notation G1:= (semG (Sem hb1 Sems Semt)).
  Notation G2:= (semG (Sem hb2 Sems Semt)).
  Variable ge1:G1.
  Variable ge2:G2.
  Variable (ge_inv: G1 -> G2 -> Prop). *)

  Context (SG TG TID SCH TR SC TC : Type).
  Variable SourceHybridMachine: @ConcurSemantics SG TID SCH TR SC mem.
  Variable TargetHybridMachine: @ConcurSemantics TG TID SCH TR TC mem.
  
  Record HybridMachine_simulation:=
    { index : Type
      ; match_state : index -> meminj -> SC -> mem -> TC -> mem -> Prop
      ; core_ord : index -> index -> Prop
      ; core_ord_wf : well_founded core_ord
    (*  ; core_initial :
          forall j c1 vals1 m1 vals2 m2,
            initial_machine hb1 Sem1 Sem2 ge1 main vals1 = Some c1 ->
            init_inv j ge1 vals1 m1 ge2 vals2 m2 ->
    exists (*mu*) cd c2,
      (*as_inj mu = j*
      /\*) initial_machine Sem2 ge2 main vals2 = Some c2
           /\ match_state cd j c1 m1 c2 m2*)
      ; thread_diagram :
          forall sge tge U st1 m1 st1' m1',
            thread_step SourceHybridMachine sge U st1 m1 st1' m1' ->
            forall cd st2 mu m2,
              match_state cd mu st1 m1 st2 m2 ->
              exists st2', exists m2', exists cd', exists mu',
                      match_state cd' mu' st1' m1' st2' m2'
                      /\ (thread_step_plus (TargetHybridMachine) tge U st2 m2 st2' m2'
               \/ (thread_step_star (TargetHybridMachine) tge U st2 m2 st2' m2' /\ core_ord cd' cd))
      ; machine_diagram :
          forall sge tge U tr st1 m1 U' tr' st1' m1',
            machine_step SourceHybridMachine sge U tr st1 m1 U' tr' st1' m1' ->
            forall cd st2 mu m2,
              match_state cd mu st1 m1 st2 m2 ->
              exists st2', exists m2', exists cd', exists mu',
                      match_state cd' mu' st1' m1' st2' m2'
                      /\ machine_step (TargetHybridMachine) tge U tr st2 m2 U' tr' st2' m2'
      ; thread_halted :
          forall cd mu U c1 m1 c2 m2 v1,
            match_state cd mu c1 m1 c2 m2 ->
            conc_halted SourceHybridMachine U c1 = Some v1 ->
            exists v2,
              conc_halted TargetHybridMachine U c2 = Some v2
      ; thread_running:
          forall cd mu c1 m1 c2 m2 ,
            match_state cd mu c1 m1 c2 m2 ->
            forall i, running_thread SourceHybridMachine c1 i <-> running_thread TargetHybridMachine c2 i
 }.
                                      
End HybridSimulation.