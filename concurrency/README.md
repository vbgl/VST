The paper "The Concurrent Permission Machine"
describes the Coq proofs in this directory (and subdirectories).

It builds in Coq 8.8.0, by "make -kj7 concurrency" from the VST root directory
  (you will need the latest ssreflect installed, that is,
   version 1.7.0 of the Mathematical Components library).

---------------------------------------
The main theorem is in concurrency/main.v;
see the "Check" command on the 2nd-to-last line:

CSL2FineBareAsm_safety:
    forall
    (CPROOF : semax_to_juicy_machine.CSL_proof)
    (Asm_prog : Asm.program),
    (compilation: CC_correct.CompCert_compiler (Clight_prog CPROOF) = Some Asm_prog)
    (asm_genv_safe : Asm_core.safe_genv x86_context.X86Context.the_ge)
    (init_mem_wd: forall m : Memory.Mem.mem,
        Genv.init_mem Asm_prog = Some m ->
        MemoryWD.valid_mem m /\
        CoreInjections.ge_wd (Renamings.id_ren m) the_ge)
    (CPROOF_initial:	
       entry_point (globalenv (Clight_prog CPROOF))
         (init_mem CPROOF)
         (Clight_safety.initial_Clight_state CPROOF)
         (Main_ptr CPROOF) [::] ->
       Clight_safety.spawn_wrapper CPROOF)
    (ConcurrentCompilerSafety: ConcurCC_safe.ConcurrentCompilerSafety_statement)
    (U : seq nat),
    exists
     (init_mem_target init_mem_target' : Memory.Mem.mem) 
     (init_thread_target : semC),
     let init_tp_target := ThreadPool.mkPool (Krun init_thread_target) tt in
     machine_semantics.initial_machine
           (EHM Asm_prog asm_genv_safe (Genv.init_mem Asm_prog))
           (Some tt) init_mem_target init_tp_target
           init_mem_target' (Main_ptr CPROOF) [::] /\
     (forall n : nat,
          HybridMachineSig.HybridFineMachine.fsafe init_tp_target
            (HybridMachineSig.diluteMem init_mem_target') U n) /\
     (forall (final_state : ThreadPool.t)
            (final_mem : Memory.Mem.mem)
            (tr : HybridMachineSig.event_trace),
          Executions.fine_execution (U, [::], init_tp_target)
            (HybridMachineSig.diluteMem init_mem_target')
            ([::], tr, final_state) final_mem ->
          SpinLocks.spinlock_synchronized tr).

Translation into English:

    Suppose CPROOF is a derivation in Concurrent Separation Logic
      that the program (Clight_prog := CSL_prog CPROOF) satisfies
      the specification (CSL_G CPROOF).
    Suppose [compilation] the CompCert compiler runs on Clight_prog,
      producing Asm_prog.
    Suppose [asm_genv_safe] that the only external "builtin" functions that
      (statically) appear in the program are malloc/free/memcpy, or any
      other function that does not modify memory.
    Suppose [init_mem_wd] the initial memory state of the program (calculated by
      CompCert's Genv.init_mem function) is well defined (this is
      easy to statically check on any particular concrete program).
    Suppose [CPROOF_initial] the initial Clight core state is a well-formed
      start state for the entry point of the "main" function (has
      appropriate formal parameter values, etc.).
    Suppose [ConcurrentCompilerSafety] the compiler translates
        safe Clight CPM executions into safe Assembly CPM executions.
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
    For any number [n], it is safe to run the fine-grain (preemptive)
        assembly language program for n steps, and
    The fine-grain (preemptive) execution is well synchronized.
  
---------------------------------------

The definitions and theorems of the paper can be found in the development as follows:

Theorem 2.1: concurrency/main.v, CSL2FineBareAsm_safety
Figure 1: control rules in concurrency/common/HybridMachineSig.v, machine_step; synchronization rules in concurrency/common/HybridMachine.v, ext_step
Definition 4.1: concurrency/common/HybridMachineSig.v, csafe
Figure 2: concurrency/common/semax_conc.v
Figure 4: msl/ghost_seplog.v
Figure 5: veric/juicy_extspec.v
Definition 6.2: veric/juicy_extspec.v, jsafeN_
Theorem 6.3: veric/semax_prog.v, semax_prog_entry_point
Figure 6: concurrency/juicy/juicy_machine.v, juicy_step and syncStep
Definition 7.1: concurrency/juicy/semax_invariant.v, state_invariant
Lemma 7.2: concurrency/juicy/semax_to_juicy_machine.v, safety_induction
Definition 7.3: concurrency/juicy/semax_to_juicy_machine.v, jmsafe
Theorem 7.4: concurrency/juicy/semax_to_juicy_machine.v, jmsafe_initial_state
Definition 7.5: concurrency/juicy/erasure_proof.v, match_st
Theorem 7.6: concurrency/juicy/erasure_proof.v
Theorem 7.7: concurrency/juicy/erasure_safety.v, Clight_initial_safe
Lemma 8.1: definition in concurrency/common/core_semantics.v, MemSem; proofs veric/Clightcore_coop.v CLC_memsem and concurrency/common/Asm_core.v Asm_mem_sem 
Hypothesis 1: concurrency/compiler/concurrent_compiler_safety_axiom.v, ConcurrentCompilerSafety_statement
Definition 9.1: concurrency/common/HybridMachineSig.v, HybridFineMachine
Definition 9.2: concurrency/sc_drf/compcert_threads_lemmas.v, sim
Lemma 9.3: concurrency/sc_drf/compcert_threads_lemmas.v, sim_internal
Definition 9.4: concurrency/sc_drf/compcert_threads_lemmas.v, weak_tsim
Theorem 9.5: concurrency/sc_drf/fineConc_safe.v, fine_safe
Lemma 9.6: concurrency/sc_drf/x86_inj.v
Theorem 9.7: concurrency/sc_drf/fineConc_safe.v, init_fine_safe
Definition 10.2: concurrency/sc_drf/spinlocks.v, spinlock_synchronized
Definition 10.4: concurrency/sc_drf/spinlocks.v, spinlock_clean
Theorem 10.6: concurrency/sc_drf/spinlocks.v, fineConc_spinlock and fineConc_clean
Theorem 11.1: concurrency/sc_drf/x86_erasure.v

---------------------------------------

The last line of concurrency/main.v is 
     Print Assumptions CSL2FineBareAsm_safety.
This is Coq's command to find all the axioms, assumptions, and "admitted" theorems, on which the proof depends.

We label them with these classes:
    [A] axioms of logic known to be consistent with CiC (and each other)
    [B] bugs in Coq's "Print Assumptions" command; see Coq issue #7192
           https://github.com/coq/coq/issues/7192       
    [D] The CompCert compiler itself; this is external.
    [E] Places where CompCert allows "wild" behavior in the form of
          unspecified inline-assembly code, unspecified builtins,
	  and unspecified external calls; CompCert's specification must
	  be modified to limit the behavior of these add-ins to
	  "memory semantics"-compatible behavior, then these assumptions
	  can be removed.
    [R] part of the axiomatization of the Real numbers, used by
        CompCert's "Flocq" floating-point library

The output of "Print Assumptions", with these labels added, is:
    [R] Rdefinitions.up
    [R] Raxioms.total_order_T
    [E] compcert_threads_lemmas.SimProofs.sim_external
    [A] Axioms.prop_ext
    [A] ProofIrrelevance.proof_irrelevance
    [A] lib.Axioms.proof_irr
    [E] Events.inline_assembly_sem
    [E] Events.inline_assembly_properties
    [E] Clightcore_coop.inline_assembly_memstep
    [A] functional_extensionality_dep
    [B] SeparationLogicSoundness.SoundSeparationLogic.CSL.func_ptr_isptr
    [B] SeparationLogicSoundness.SoundSeparationLogic.CSL.func_ptr_def
    [B] SeparationLogicSoundness.SoundSeparationLogic.CSL.func_ptr
    [E] Events.external_functions_sem
    [E] Events.external_functions_properties
    [E] Clightcore_coop.extcall_sem_mem_step
    [E] ClightSemanticsForMachines.extcall_ev_elim
    [A] Eqdep.Eq_rect_eq.eq_rect_eq
    [R] Raxioms.completeness
    [A] Classical_Prop.classic
    [R] Raxioms.archimed
    [B] SeparationLogicSoundness.SoundSeparationLogic.CSL.approx_func_ptr
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
    [R] Rdefinitions.R0
    [R] Rdefinitions.R
    [D] CC_correct.CompCert_compiler
