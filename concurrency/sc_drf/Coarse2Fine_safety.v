Require Import VST.concurrency.common.x86_context.
Require Import VST.concurrency.common.HybridMachineSig.
Require Import VST.concurrency.common.HybridMachine.
Require Import VST.concurrency.common.erased_machine.
Require Import VST.concurrency.common.threadPool.

Import dry_context.AsmContext.
Import HybridMachineSig.
Import X86Context.

Section Coarse2FineAsm_safety.
  
  Context (Asm_prog: Asm.program).
  Context (asm_genv_safe: Asm_core.safe_genv (@the_ge Asm_prog)).
  Definition x86Sem:=@X86Sem Asm_prog asm_genv_safe.
  
Lemma Coarse2FineAsm_safety:
    forall U Main_ptr,
    forall init_mem_target init_thread_target,
      Asm.entry_point (Globalenvs.Genv.globalenv Asm_prog)
                      init_mem_target init_thread_target Main_ptr nil ->
    let res_target := permissions.getCurPerm init_mem_target in
    let init_tp_target :=
        DryHybridMachine.initial_machine
          (Sem:=x86Sem)
          res_target init_thread_target
         in
  let init_MachState_target := (U, nil, init_tp_target) in 
  (forall n,
    HybridMachineSig.HybridMachineSig.HybridCoarseMachine.csafe
      (ThreadPool:=threadPool.OrdinalPool.OrdinalThreadPool
                     (resources:=DryHybridMachine.dryResources)
                     (Sem:=x86_context.X86Context.X86Sem Asm_prog asm_genv_safe))
      (machineSig:= HybridMachine.DryHybridMachine.DryHybridMachineSig)
      init_MachState_target init_mem_target n)->
  let init_tp_bare :=
      ThreadPool.mkPool
        (resources:=BareMachine.resources)
        (Sem:=x86Sem)
        (Krun init_thread_target) tt  in
  forall n,
    HybridMachineSig.HybridMachineSig.HybridFineMachine.fsafe
      (dilMem:= BareDilMem)
      (ThreadPool:=threadPool.OrdinalPool.OrdinalThreadPool
                     (resources:=erased_machine.BareMachine.resources)
                     (Sem:=x86Sem))
      (machineSig:= BareMachine.BareMachineSig)
      init_tp_bare init_mem_target U n.
Proof.
Admitted.

End Coarse2FineAsm_safety.