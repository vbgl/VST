Require Import compcert.common.Globalenvs.
Require Import compcert.common.ExposedSimulations.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.

Require Import VST.concurrency.common.permissions.
Require Import VST.concurrency.compiler.concurrent_compiler_simulation.
Require Import VST.concurrency.compiler.sequential_compiler_correct.
Require Import VST.concurrency.compiler.CoreSemantics_sum.
Require Import VST.concurrency.common.HybridMachine.
Require Import VST.concurrency.compiler.HybridMachine_simulation.


(*Clight Machine *)
Require Import VST.concurrency.common.ClightMachine.
(*Asm Machine*)
Require Import VST.concurrency.common.x86_context.
(*

(** *One thread simulation*)
Module ThreadedSimulation (CC_correct: CompCert_correctness).
  
  Import HybridMachineSig.
  Import DryHybridMachine.

  Existing Instance OrdinalPool.OrdinalThreadPool.

  (** *C Semantics*)
  Context (C_program: Clight.program).
  Definition Clight_g : Clight.genv := Clight.globalenv C_program.
  Definition CSem : Semantics := ClightSemantincsForMachines.ClightSem Clight_g.

  
  (** *Asm Semantics*)
  Import X86Context.
  (*Import the Asm Hybrid Machine*)
  Context (Asm_program: Asm.program).
  Definition Asm_g := (@the_ge Asm_program).
  Context (Asm_genv_safe: Asm_core.safe_genv (@the_ge Asm_program)).

  
  (** *AsHybrid Semantics and Machine*)
  Definition AsmSem : Semantics := @X86Sem Asm_program Asm_genv_safe.

  (** The hybrid semantics*)
  Instance HybridSem h : Semantics := CoreSem_Sum h CSem AsmSem.
  Existing Instance dryResources.
  Notation TP h := (threadPool.OrdinalPool.OrdinalThreadPool(Sem:=HybridSem h)).
  Existing Instance DryHybridMachineSig.
  Definition HybMachine h:=
    HybridMachineSig.HybridCoarseMachine.HybridCoarseMachine
      (ThreadPool:= TP h).
  Definition HybConcSem h:=
    HybridMachineSig.ConcurMachineSemantics(HybridMachine:=HybMachine h).
  Notation ThreadPool n :=
    (ThreadPool.t(Sem:= HybridSem n)).


  (** *Extracting index and match relation from CompCert*)
  Context (compiled: 
             CC_correct.CompCert_compiler C_program = Some Asm_program).
  Definition compiler_sim:= CC_correct.simpl_clight_semantic_preservation _ _ compiled.
  Definition compiler_index: Type:= Injindex compiler_sim.
  Definition compiler_match:= Injmatch_states compiler_sim.
  
  Section CompileOneThread.
    Import OrdinalPool.
    Variable match_thread_source: forall n,
        meminj -> @ctl (@semC (HybridSem (Some n))) -> mem -> @ctl (@semC (HybridSem (Some (S n)))) -> mem -> Prop.
    Variable match_thread_target: forall n,
        meminj -> @ctl (@semC (HybridSem (Some n))) -> mem -> @ctl (@semC (HybridSem (Some (S n)))) -> mem -> Prop.
    Inductive match_thread_compiled n:
      option compiler_index -> meminj -> @ctl (@semC (HybridSem (Some n))) -> mem -> @ctl (@semC (HybridSem (Some (S n)))) -> mem -> Prop  :=
    | Build_match_thread_compiled:
        forall i j st1 m1 st2 m2,
        compiler_match i j (Smallstep.set_mem st1 m1) (Smallstep.set_mem st2 m2) ->
        match_thread_compiled n (Some i) j st1 m1 st2 m2.
      

  Definition FST {A B} (HH : A /\ B):=
    fst (ssrfun.pair_of_and HH).

  Definition SND {A B} (HH : A /\ B):=
    snd (ssrfun.pair_of_and HH).
    
    Record concur_match hb (ocd: option compiler_index)
       (j:meminj) (cstate1: ThreadPool (Some hb)) (m1: Mem.mem) (cstate2: ThreadPool(Some (S hb))) (m2: mem):=
  { same_length: num_threads cstate1 = num_threads cstate2
    ; memcompat1: mem_compatible cstate1 m1
    ; memcompat2: mem_compatible cstate2 m2
    ; mtch_source:
        forall (i:nat),
          (i > hb)%nat ->
          forall (cnti1: containsThread cstate1 i)
            (cnti2: containsThread cstate2 i),
          match_thread_source hb j
                              (getThreadC cnti1)
                              (permissions.restrPermMap (FST (memcompat1 i cnti1)))
                              (getThreadC cnti2)
                              (permissions.restrPermMap (FST (memcompat2 i cnti2)))
    ; mtch_target:
        forall (i:nat),
          (i < hb)%nat ->
          forall (cnti1: containsThread cstate1 i)
            (cnti2: containsThread cstate2 i),
          match_thread_target  hb j
                              (getThreadC cnti1)
                              (restrPermMap (FST(memcompat1 i cnti1)))
                              (getThreadC cnti2)
                              (permissions.restrPermMap (FST(memcompat2 i cnti2)))
    ; mtch_compiled:
        forall (i:nat),
          (i = hb)%nat ->
          forall (cnti1: containsThread cstate1 i)
            (cnti2: containsThread cstate2 i),
            exists cd, ocd = Some cd /\
                  match_thread_compiled cd j
                                (getThreadC cnti1)
                                (restrPermMap (FST(memcompat1 i cnti1)))
                                (getThreadC cnti2)
                                (restrPermMap (FST(memcompat2 i cnti2))) }.
    
    Variable match_state: forall n,
      index ->
      Values.Val.meminj ->
      ThreadPool (Some n) -> Memory.Mem.mem -> ThreadPool (Some (S n)) -> Memory.Mem.mem -> Prop.
    
    Lemma compile_one_thread:
      forall n m,
        HybridMachine_simulation_properties
          (HybConcSem (Some n) m)
          (HybConcSem (Some (S n)) m)
          (match_state n).
    Proof.
      intros.
    Admitted.

  End CompileOneThread.

  
  Section CompileNThreads.

    
 Variable index: nat -> Type.
 Variable match_state: forall n,
     index n ->
     Values.Val.meminj ->
     ThreadPool (Some 0) -> Memory.Mem.mem -> ThreadPool (Some n) -> Memory.Mem.mem -> Prop.
 
  Lemma compile_n_threads:
      forall n m,
        HybridMachine_simulation.HybridMachine_simulation_properties
          (HybConcSem (Some 0) m)
          (HybConcSem (Some n) m)
          (match_state n).
    Proof.
      intros.
    Admitted.

  End CompileNThreads.

 Section CompileInftyThread.
    
 Variable index: nat -> Type.
 Variable match_state: forall n,
     index n ->
     Values.Val.meminj ->
     ThreadPool (Some 0) -> Memory.Mem.mem -> ThreadPool (Some n) -> Memory.Mem.mem -> Prop.
 
  Lemma compile_all_threads:
      forall n m,
        HybridMachine_simulation.HybridMachine_simulation_properties
          (HybConcSem (Some 0) m)
          (HybConcSem None m)
          (match_state n).
    Proof.
      intros.
    Admitted.

  End CompileInftyThread.



  
  
      
  
(*  Lemma ConcurrentCompilerCorrectness:
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
End ThreadedSimulation.
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