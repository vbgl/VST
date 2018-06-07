Require Import VST.concurrency.common.x86_context.
Require Import VST.concurrency.common.HybridMachineSig.
Require Import VST.concurrency.juicy.erasure_proof.

Import dry_context.AsmContext.
Import HybridMachineSig.

Section Coarse2FineAsm_safety.
  
  Context (Asm_prog: Asm.program).
  Context (asm_genv_safe: Asm_core.safe_genv (x86_context.X86Context.the_ge Asm_prog)).

  
Lemma Coarse2FineAsm_safety:
    forall U,
    forall init_mem_target init_thread_target,
    let res_target := permissions.getCurPerm init_mem_target in
  let init_tp_target :=
      threadPool.ThreadPool.mkPool
        (resources:=HybridMachine.DryHybridMachine.dryResources)
        (threadPool.Krun init_thread_target)
        (res_target, permissions.empty_map) in
  let init_MachState_target := (U, nil, init_tp_target) in 
  (forall n,
    HybridMachineSig.HybridMachineSig.HybridCoarseMachine.csafe
      (ThreadPool:=threadPool.OrdinalPool.OrdinalThreadPool
                     (resources:=HybridMachine.DryHybridMachine.dryResources)
                     (Sem:=x86_context.X86Context.X86Sem Asm_prog asm_genv_safe))
      (machineSig:= HybridMachine.DryHybridMachine.DryHybridMachineSig)
      init_MachState_target init_mem_target n)->
  forall n,
    HybridMachineSig.HybridMachineSig.HybridFineMachine.fsafe
      (dilMem:= BareDilMem)
      (ThreadPool:=threadPool.OrdinalPool.OrdinalThreadPool
                     (resources:=erasure_proof.Parching.DR)
                     (Sem:=x86_context.X86Context.X86Sem Asm_prog asm_genv_safe))
      (machineSig:= HybridMachine.DryHybridMachine.DryHybridMachineSig)
      init_tp_target init_mem_target U n.
Proof.
Admitted.

End Coarse2FineAsm_safety.