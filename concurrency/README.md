The paper "Compiler Correctness for Concurrency" (July 11, 2018)
describes the Coq proofs in this directory (and subdirectories).

It builds in Coq 8.8.0, by "make -kj7 concurrency" from the VST root directory
  (you will need the latest ssreflect installed, that is,
   version 1.7.0 of the Mathematical Components library).

---------------------------------------
The main theorem is in concurrency/main.v:

    CSL2FineBareAsm_safety: (* THE MAIN THEOREM *)
    forall
    (CPROOF : semax_to_juicy_machine.CSL_proof)
    (Asm_prog : Asm.program)
    (compilation: CC_correct.CompCert_compiler (Clight_prog CPROOF) =
              Some Asm_prog)
    (asm_genv_safe : Asm_core.safe_genv x86_context.X86Context.the_ge)
    (init_mem_wd: forall m : Memory.Mem.mem,
          Genv.init_mem Asm_prog = Some m ->
          MemoryWD.valid_mem m /\
	  CoreInjections.ge_wd (Renamings.id_ren m) the_ge)
    (CPROOF_initial: entry_point (globalenv (Clight_prog CPROOF)) 
         (init_mem CPROOF) (Clight_safety.initial_Clight_state CPROOF)
         (Main_ptr CPROOF) [::])
    (U : seq nat),
    exists
      (init_mem_target : Memory.Mem.mem) 
      (init_mem_target' : Memory.Mem.mem) 
      (init_thread_target : semC),
    let init_tp_target :=
           ThreadPool.mkPool (Krun init_thread_target) tt in
     machine_semantics.initial_machine
           (EHM Asm_prog asm_genv_safe (Genv.init_mem Asm_prog)) 
           (Some tt) init_mem_target init_tp_target init_mem_target'
           (Main_ptr CPROOF) [::] /\
     (forall n : nat,
       HybridMachineSig.HybridFineMachine.fsafe init_tp_target
            (HybridMachineSig.diluteMem init_mem_target') U n)

Translation into English:

    Suppose CPROOF is a derivation in Concurrent Separation Logic
      that the program (Clight_prog := CSL_prog CPROOF) satisfies
      the specification (CSL_G CPROOF).
    Suppose [compilation] the CompCert compiler runs on Clight_prog,
      producing Asm_prog.
    Suppose [asm_genv_safe] that the only external "builtin" functions that
      (statically) appear in the program are malloc/free/memcpy, or any
      other function that does not modify memory.
    Suppose [init_mem-wd] the initial memory state of the program (calculated by
      CompCert's Genv.init_mem function) is well defined (this is
      easy to statically check on any particular concrete program).
    Suppose [CPROOF_initial] the initial Clight core state is a well-formed
      start state for the entry point of the "main" function (has
      appropriate formal parameter values, etc.).
    Suppose [U] is an arbitrary preemptive schedule.
    THEN
    There exists an assembly-language initial memory [init_mem_target]
      that is has all the initialized extern global variables as specified
      in the program;
    There exists a memory [init_mem_target'] that has in addition the
      stack frame of the main function;
    There exists an initial register bank [init_thread_target] at the entry    
      of the main function;
    We construct an initial thread pool [init_tp_target];
    Such that [machine_semantics.initial_machine...] the machine state is
      now a proper initial state for the program Asm_prog; and
    For any number [n],
    It is safe to run the fine-grain (preemptive) assembly language program
       for n steps.
  
---------------------------------------

The last line of concurrency/main.v is 
     Print Assumptions CSL2FineBareAsm_safety,
which mentions the following axioms, categorized into
    [A] axioms of logic known to be consistent with CiC (and each other)
    [B] bugs in Coq's print_assumptions command; see Coq issue #7192
           https://github.com/coq/coq/issues/7192       
    [C] abstract parameters of CompCert, instantiated for any particular
          machine such as x86_32
    [D] The CompCert compiler itself; this is external (and supplied
         in our branch of the CompCert repo)
    [R] part of the axiomatization of the Real numbers, used by
        CompCert's "Flocq" floating-point library
    [H] holes in our proof

  
    [R] Rdefinitions.up
    [R] Raxioms.total_order_T
    [H] BareMachine.syncstep_equal_run (Nick)
    [H] Asm.semantics_determinate (William and Nick)
    [A] Axioms.prop_ext
    [A] ProofIrrelevance.proof_irrelevance
    [A] lib.Axioms.proof_irr
    [H] safety.preservation  (Santiago)
    [H] safety_equivalence.ksafe_csafe_equiv' (Santiago)
    [C] Events.inline_assembly_sem
    [H] x86_erasure.X86CoreErasure.inline_assembly_erasure (Nick)
    [H] ConcurCC_safe.initial_csafe_all_schedule (Santiago)
    [A] functional_extensionality_dep
    [B] SeparationLogicSoundness.SoundSeparationLogic.CSL.func_ptr_isptr
    [B] SeparationLogicSoundness.SoundSeparationLogic.CSL.func_ptr_def
    [B] SeparationLogicSoundness.SoundSeparationLogic.CSL.func_ptr
    [H] x86_erasure.X86CoreErasure.extsem_erasure (Nick)
    [C] Events.external_functions_sem
    [H] ConcurCC_safe.explicit_safety_step  (Santiago)
    [A] Eqdep.Eq_rect_eq.eq_rect_eq
    [H] X86Inj.corestep_wd  (Nick)
    [H] X86Inj.corestep_obs_eq (Nick)
    [H] x86_context.X86SEMAxioms.corestep_det (Nick) 
    [R] Raxioms.completeness
    [A] Classical_Prop.classic
    [R] Raxioms.archimed
    [B] SeparationLogicSoundness.SoundSeparationLogic.CSL.approx_func_ptr
    [H] safety.X_dec : forall (X : Type) (x y : X), {x = y} + {x <> y}
    [R] Raxioms.Rplus_opp_r
    [R] Raxioms.Rplus_lt_compat_l
    [R] Raxioms.Rplus_comm
    [R] Raxioms.Rplus_assoc
    [R] Raxioms.Rplus_0_l
    [R] Rdefinitions.Rplus
    [R] Rdefinitions.Ropp
    [R] Raxioms.Rmult_plus_distr_l
    [R] Raxioms.Rmult_lt_compat_l
    [R] Raxioms.Rmult_comm
    [R] Raxioms.Rmult_assoc
    [R] Raxioms.Rmult_1_l
    [R] Rdefinitions.Rmult
    [R] Raxioms.Rlt_trans
    [R] Raxioms.Rlt_asym
    [R] Rdefinitions.Rlt
    [R] Raxioms.Rinv_l
    [R] Rdefinitions.Rinv
    [R] Raxioms.R1_neq_R0
    [R] Rdefinitions.R1
    [R} Rdefinitions.R0
    [R] Rdefinitions.R
    [H] ConcurCC_safe.ConcurCC_correct.ConcurrentCompilerCorrectness  (Santiago)
    [D] CC_correct.CompCert_compiler : program -> option Asm.program
    [H] Clight_safety.Clight_new_Clight_safety_gen  (William)
    [H] ConcurCC_safe.Clight_finite_branching  (Santiago)
    [H] ClightSemantincsForMachines.CLC_evsem_obligation_5 (Lennart)
    [H] ClightSemantincsForMachines.CLC_evsem_obligation_4 (Lennart)
    [H] ClightSemantincsForMachines.CLC_evsem_obligation_3 (Lennart)
    [H] ClightSemantincsForMachines.CLC_evsem_obligation_2 (Lennart)
    [H] ClightSemantincsForMachines.CLC_evsem_obligation_1 (Lennart)
