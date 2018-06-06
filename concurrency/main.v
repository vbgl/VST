(* Main File putting all together. *)

Require Import VST.concurrency.juicy.erasure_safety.

Require Import VST.concurrency.compiler.concurrent_compiler_safety_proof.
Require Import VST.concurrency.compiler.sequential_compiler_correct.



Module Main (CC_correct: CompCert_correctness).
  (*Import the *)
  (*Import the safety of the compiler for concurrent programs*)
  Module ConcurCC_safe:= (Concurrent_Safety CC_correct).
  Import ConcurCC_safe.
  
  (*Assumptions *)
  Context (CPROOF : semax_to_juicy_machine.CSL_proof).
  Definition Clight_prog:= semax_to_juicy_machine.CSL_prog CPROOF. 
  Context (Asm_prog: Asm.program).
  Context (asm_genv_safe: Asm_core.safe_genv (x86_context.X86Context.the_ge Asm_prog)).
  Context (compilation : CC_correct.CompCert_compiler Clight_prog = Some Asm_prog).

  (*Safety from CSL to Coarse Asm*)
  Lemma CSL2CoarseAsm_safety:
    forall U,
    exists init_mem_target init_thread_target,
    let res_target := permissions.getCurPerm init_mem_target in
  let init_tp_target :=
      threadPool.ThreadPool.mkPool
        (resources:=erasure_proof.Parching.DR)
        (threadPool.Krun init_thread_target)
      (res_target, permissions.empty_map) in
  let init_MachState_target := (U, nil, init_tp_target) in  
  forall n,
    HybridMachineSig.HybridMachineSig.HybridCoarseMachine.csafe
      (ThreadPool:=threadPool.OrdinalPool.OrdinalThreadPool
                     (Sem:=x86_context.X86Context.X86Sem Asm_prog asm_genv_safe))
      (machineSig:= HybridMachine.DryHybridMachine.DryHybridMachineSig)
      init_MachState_target init_mem_target n.
  Proof.
    intros.
    eapply ConcurrentCompilerSafety.
    3: eapply Clight_initial_safe.
    - eexact compilation.
    - instantiate(1:=nil).
      instantiate (2:=Clight.globalenv Clight_prog).
      simpl.
      
      (* This is should follow from CPROOF, and should be proven in folder juicy*)
      admit. 
  Admitted.

End Main.


(* Test an instantiation of Main theorem. *)
Module CC_correct: CompCert_correctness.
  Axiom CompCert_compiler : Clight.program -> option Asm.program.
  Axiom simpl_clight_semantic_preservation :
    forall (p : Clight.program) (tp : Asm.program),
      CompCert_compiler p = Some tp ->
      ExposedSimulations.fsim_properties_inj (Clight.semantics2 p) (Asm.semantics tp)
                                             Clight.get_mem Asm.get_mem.

End CC_correct.

Module Test_Main:= (Main CC_correct).
Import Test_Main.
Print Assumptions CSL2CoarseAsm_safety.