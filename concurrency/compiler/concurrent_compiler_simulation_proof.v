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

Require Import VST.concurrency.compiler.Clight_self_simulation.
Require Import VST.concurrency.compiler.Asm_self_simulation.



Set Bullet Behavior "Strict Subproofs".

(*Clight Machine *)
Require Import VST.concurrency.common.ClightMachine.
(*Asm Machine*)
Require Import VST.concurrency.common.x86_context.

(** *One thread simulation*)
Module ThreadedSimulation (CC_correct: CompCert_correctness).
  
  Import HybridMachineSig.
  Import DryHybridMachine.

  Existing Instance OrdinalPool.OrdinalThreadPool.
  Existing Instance HybridMachineSig.HybridCoarseMachine.DilMem.

  (** *C Semantics*)
  Context (C_program: Clight.program).
  Definition Clight_g : Clight.genv := Clight.globalenv C_program.
  Definition CSem : Semantics := ClightSemantincsForMachines.ClightSem Clight_g.
  Definition Cself_simulation := clight_self_simulation Clight_g.
  Definition Clight_code_inject := self_simulation.code_inject _ _ Cself_simulation.
  Definition Clight_match := self_simulation.match_self Clight_code_inject.
  
  (** *Asm Semantics*)
  Import X86Context.
  (*Import the Asm Hybrid Machine*)
  Context (Asm_program: Asm.program).
  Definition Asm_g := (@the_ge Asm_program).
  Context (Asm_genv_safe: Asm_core.safe_genv (@the_ge Asm_program)).
  Definition Aself_simulation := Asm_self_simulation Asm_g.
  Definition Asm_code_inject := self_simulation.code_inject _ _ Aself_simulation.
  Definition Asm_match := self_simulation.match_self Asm_code_inject.

  
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
  Definition compiler_match (i:compiler_index) (j:meminj)
       (c1:  Smallstep.state (Smallstep.part_sem (Clight.semantics2 C_program)))
       (m1: mem)
       (c2: Smallstep.state (Asm.part_semantics Asm_g))
       (m2: mem): Prop
    := Injmatch_states compiler_sim i j
                       (Smallstep.set_mem c1 m1)
                       (Smallstep.set_mem c2 m2).

  (* Compiler match that holds under interference of other threads. *)
  Inductive compiler_match_padded:
    compiler_index -> meminj -> Smallstep.state (Smallstep.part_sem (Clight.semantics2 C_program)) ->
    mem -> Smallstep.state (Asm.part_semantics Asm_g) -> mem -> Prop
    :=
    | BuildCompilerMatch: forall cd j1 j2 j3 j s1 m1 s2 m2 s3 m3 s4 m4,
        Clight_match j1 s1 m1 s2 m2 ->
        compiler_match cd j2 s2 m2 s3 m3 ->
        Asm_match j3 s3 m3 s4 m4 ->
        compose_meminj (compose_meminj j1 j2) j3 = j ->
        compiler_match_padded cd j s1 m1 s4 m4.

  Context (hb: nat).
  Definition SemTop: Semantics:= (HybridSem (Some hb)).
  Definition SemBot: Semantics:= (HybridSem (Some (S hb))).
  
  Section CompileOneThread.
    Import OrdinalPool.

    Inductive match_state2match_thread
              {sem1 sem2: Semantics}
              (SState: @semC sem1 -> state_sum (@semC CSem) (@semC AsmSem))
              (TState: @semC sem2 -> state_sum (@semC CSem) (@semC AsmSem))
              (match_state : meminj -> @semC sem1 -> mem -> @semC sem2 -> mem -> Prop) :
    meminj ->
    @ctl (@semC SemTop) -> mem ->
    @ctl (@semC SemBot) -> mem -> Prop  :=
  | CThread_Running: forall j code1 m1 code2 m2,
      match_state j code1 m1 code2 m2 ->
      match_state2match_thread SState TState match_state j (Krun (SState code1)) m1
                            (Krun (TState code2)) m2
  | CThread_Blocked: forall j code1 m1 code2 m2,
      match_state j code1 m1 code2 m2 ->
      match_state2match_thread SState TState match_state j (Kblocked (SState code1)) m1
                            (Kblocked (TState code2)) m2
  | CThread_Resume: forall j code1 m1 code2 m2 v v',
      match_state2match_thread SState TState match_state j (Kresume (SState code1) v) m1
                            (Kresume (TState code2) v') m2
  | CThread_Init: forall j m1 m2 v1 v1' v2 v2',
      Val.inject j v1 v2 ->
      Val.inject j v1' v2' ->
      match_state2match_thread SState TState match_state j (Kinit v1 v1') m1
                               (Kinit v1 v1') m2.
    
    Definition SST := SState (@semC CSem) (@semC AsmSem).
    Definition TST := TState (@semC CSem) (@semC AsmSem).
    
    Definition match_thread_source:
      meminj -> @ctl (@semC SemTop) -> mem -> @ctl (@semC SemBot) -> mem -> Prop:=
      match_state2match_thread SST SST
                               Clight_match.
    Definition match_thread_target:
      meminj -> @ctl (@semC SemTop) -> mem -> @ctl (@semC SemBot) -> mem -> Prop:=
      match_state2match_thread TST TST
                               Asm_match.
    Definition match_thread_compiled cd:
      meminj -> @ctl (@semC SemTop) -> mem -> @ctl (@semC SemBot) -> mem -> Prop:=
      match_state2match_thread SST TST
                               (compiler_match_padded cd).

    (* NOTE: Old version*)
  (* Inductive match_thread_compiled:
    compiler_index -> meminj ->
    @ctl (@semC SemTop) -> mem ->
    @ctl (@semC SemBot) -> mem -> Prop  :=
  | CThread_Running': forall cd j code1 m1 code2 m2,
      compiler_match cd j (Smallstep.set_mem code1 m1) (Smallstep.set_mem code2 m2) ->
      match_thread_compiled cd j (Krun (SState _ _ code1)) m1
                            (Krun (TState _ _ code2)) m2
  | CThread_Blocked': forall cd j code1 m1 code2 m2,
      compiler_match cd j (Smallstep.set_mem code1 m1) (Smallstep.set_mem code2 m2) ->
      match_thread_compiled  cd j (Kblocked (SState _ _ code1)) m1
                            (Kblocked (TState _ _ code2)) m2
  | CThread_Resume': forall cd j code1 m1 code2 m2 v v',
      (*Do I need to keep this two? Probanly not*)
      (*semantics.at_external (CoreSem Sems) genvS code1 m1 = Some (f,ls1) ->
      semantics.at_external (CoreSem Semt) genvT code2 m2 = Some (f',ls2) ->
      Val.inject_list j ls1 ls2 ->
      semantics.after_external (CoreSem Sems) genvS None code1 = Some code1' ->
      semantics.after_external (CoreSem Semt) genvT None code2 = Some code2' -> *)
      compiler_match cd j (Smallstep.set_mem code1 m1) (Smallstep.set_mem code2 m2) ->
      match_thread_compiled cd j (Kresume (SState _ _ code1) v) m1
                            (Kresume (TState _ _ code2) v') m2
  | CThread_Init': forall cd j m1 m2 v1 v1' v2 v2',
      Val.inject j v1 v2 ->
      Val.inject j v1' v2' ->
      match_thread_compiled cd j (Kinit v1 v1') m1
                            (Kinit v2 v2') m2. *)
    
    Record concur_match (ocd: option compiler_index)
       (j:meminj) (cstate1: ThreadPool (Some hb)) (m1: Mem.mem) (cstate2: ThreadPool(Some (S hb))) (m2: mem):=
  { same_length: num_threads cstate1 = num_threads cstate2
    ; memcompat1: mem_compatible cstate1 m1
    ; memcompat2: mem_compatible cstate2 m2
    ; taret_invariant: invariant cstate2
    ; mtch_source:
        forall (i:nat),
          (i > hb)%nat ->
          forall (cnti1: containsThread cstate1 i)
            (cnti2: containsThread cstate2 i),
          match_thread_source j
                              (getThreadC cnti1)
                              (permissions.restrPermMap (proj1 (memcompat1 i cnti1)))
                              (getThreadC cnti2)
                              (permissions.restrPermMap (proj1 (memcompat2 i cnti2)))
    ; mtch_target:
        forall (i:nat),
          (i < hb)%nat ->
          forall (cnti1: containsThread cstate1 i)
            (cnti2: containsThread cstate2 i),
          match_thread_target  j
                              (getThreadC cnti1)
                              (restrPermMap (proj1(memcompat1 i cnti1)))
                              (getThreadC cnti2)
                              (permissions.restrPermMap (proj1(memcompat2 i cnti2)))
    ; mtch_compiled:
        forall (i:nat),
          (i = hb)%nat ->
          forall (cnti1: containsThread cstate1 i)
            (cnti2: containsThread cstate2 i),
            exists cd, ocd = Some cd /\
                  match_thread_compiled cd j
                                        (getThreadC cnti1)
                                        (restrPermMap (proj1 (memcompat1 i cnti1)))
                                        (getThreadC cnti2)
                                        (restrPermMap (proj1 (memcompat2 i cnti2))) }.

    
    Lemma contains12:
      forall {data j cstate1 m1 cstate2 m2},
        concur_match data j cstate1 m1 cstate2 m2 ->
        forall {i:nat} (cnti1: containsThread cstate1 i),
          containsThread cstate2 i.
    Proof.
      unfold containsThread.
      intros ? ? ? ? ? ? H. destruct H.
      rewrite same_length0; auto.
    Qed.

    Lemma contains21:
      forall {data j cstate1 m1 cstate2 m2},
        concur_match data j cstate1 m1 cstate2 m2 ->
        forall {i:nat} (cnti1: containsThread cstate2 i),
          containsThread cstate1 i.
    Proof.
      unfold containsThread.
      intros ? ? ? ? ? ? H. destruct H.
      rewrite same_length0; auto.
    Qed.
    
    Lemma concur_match_same_running:
      forall (m : option mem) (cd : option compiler_index) (mu : meminj)
        (c1 : ThreadPool (Some hb)) (m1 : mem) (c2 : ThreadPool (Some (S hb))) 
        (m2 : mem),
        concur_match cd mu c1 m1 c2 m2 ->
        forall i : nat,
          machine_semantics.running_thread (HybConcSem (Some hb) m) c1 i <->
          machine_semantics.running_thread (HybConcSem (Some (S hb)) m) c2 i.
    Proof.
      intros.
      pose proof (@contains12 _ _ _ _ _ _ H) as CNT12.
      pose proof (@contains21 _ _ _ _ _ _ H) as CNT21.
      inversion H; simpl.
      split; intros H0 ? ? ? ?.
      - destruct (Compare_dec.lt_eq_lt_dec j hb) as [[?|?]|?].  
        + specialize (mtch_target0 j l (CNT21 _ cnti) cnti).
    Admitted.

    Inductive ord_opt {A} (ord: A -> A -> Prop): option A -> option A -> Prop:=
    | Some_ord:
        forall x y, ord x y -> ord_opt ord (Some x) (Some y).
    
    Lemma option_wf:
      forall A (ord: A -> A -> Prop),
        well_founded ord ->
        well_founded (ord_opt ord).
    Proof.
      unfold well_founded.
      intros.
      destruct a.
      2: econstructor; intros; inversion H0.
      specialize (H a).
      induction H.
      econstructor; intros.
      inversion H1; subst.
      eapply H0; eauto.
    Qed.


    
    Inductive individual_match ocd i:
      meminj -> ctl -> mem -> ctl -> mem -> Prop:= 
    |individual_mtch_source:
       (i > hb)%nat ->
       forall j s1 m1 s2 m2,
         match_thread_source j s1 m1 s2 m2 ->
         individual_match ocd i j s1 m1 s2 m2
    |individual_mtch_target:
       (i < hb)%nat ->
       forall j s1 m1 s2 m2,
         match_thread_target j s1 m1 s2 m2 ->
         individual_match ocd i j s1 m1 s2 m2
    | individual_mtch_compiled:
        (i = hb)%nat ->
        forall cd j s1 m1 s2 m2,
          ocd = Some cd ->
          match_thread_compiled cd j s1 m1 s2 m2 ->
          individual_match ocd i j s1 m1 s2 m2.
    
    Lemma Concur_update:
      forall (st1 : t) (m1 m' : mem) (tid : nat) (Htid : containsThread st1 tid)
        c1 (cd cd' : option compiler_index) (st2 : t) 
        (mu : meminj) (m2 : mem)
        c2
        (f' : meminj) (m2' : mem) (Htid' : containsThread st2 tid),
        concur_match cd mu st1 m1 st2 m2 ->
        individual_match cd' tid f' c1 m' c2 m2' ->
        self_simulation.is_ext mu (Mem.nextblock m1) f' (Mem.nextblock m2) ->
        concur_match cd' f'
                     (updThread Htid c1
                                (getCurPerm m', snd (getThreadR Htid))) m'
                     (updThread Htid' c2
                                (getCurPerm m2', snd (getThreadR Htid'))) m2'.
    Proof.
    Admitted.

    
        Ltac exploit_match:=
        unfold match_thread_target,match_thread_source,match_thread_compiled in *;
        match goal with
        | [ H: getThreadC ?i = _ ?c,
               H0: context[match_state2match_thread] |- _ ] =>
          rewrite H in H0; inversion H0; subst; simpl in *
        end;
        fold match_thread_target in *;
        fold match_thread_source in *;
        fold match_thread_compiled in *.

        (* Build the concur_match *)
        Ltac destroy_ev_step_sum:=
          match goal with
          | [ H: ev_step_sum _ _ _ _ _ _ _ |- _ ] => inversion H; subst
          end.
        
    (* When a thread takes an internal step (i.e. not changing the schedule) *)
    Lemma internal_step_diagram:
      forall (m : option mem) (sge tge : HybridMachineSig.G) (U : list nat)
        (st1 : ThreadPool (Some hb)) (m1 : mem) (st1' : ThreadPool (Some hb)) 
        (m1' : mem),
        machine_semantics.thread_step (HybConcSem (Some hb) m) sge U st1 m1 st1' m1' ->
        forall (cd : option compiler_index) (st2 : ThreadPool (Some (S hb))) 
          (mu : meminj) (m2 : mem),
          concur_match cd mu st1 m1 st2 m2 ->
          exists
            (st2' : ThreadPool (Some (S hb))) (m2' : mem) (cd' : option compiler_index) 
            (mu' : meminj),
            concur_match cd' mu' st1' m1' st2' m2' /\
            (machine_semantics_lemmas.thread_step_plus
               (HybConcSem (Some (S hb)) m) tge U st2 m2
               st2' m2' \/
             machine_semantics_lemmas.thread_step_star
               (HybConcSem (Some (S hb)) m) tge U st2 m2
               st2' m2' /\ ord_opt (Injorder compiler_sim) cd' cd).
    Proof.
      intros.
      inversion H; subst.
      inversion Htstep; subst.
      destruct (Compare_dec.lt_eq_lt_dec tid hb) as [[?|?]|?].  
      - (* tid < hb *)
        pose proof (mtch_target _ _ _ _ _ _ H0 _ l Htid (contains12 H0 Htid)) as HH.
        simpl in *.
        exploit_match.
        destroy_ev_step_sum; simpl in *.
        simpl.
        eapply Asm_event.asm_ev_ax1 in H2.
        replace Hcmpt with (memcompat1 cd mu st1 m1 st2 m2 H0) in H2 by eapply Axioms.proof_irr.
        instantiate (1:=Asm_genv_safe) in H2.
        
        eapply Aself_simulation in H5; eauto.
        destruct H5 as (c2' & f' & t' & m2' & (CoreStep & MATCH & is_ext & inject_incr)).

        eapply Asm_event.asm_ev_ax2 in CoreStep; try eapply Asm_genv_safe.
        destruct CoreStep as (?&?); eauto.
         
        (* contains.*)
        pose proof (@contains12  _ _ _ _ _ _  H0 _ Htid) as Htid'.

        (* Construct the new thread pool *)
        exists (updThread Htid' (Krun (TState Clight.state Asm.state c2'))
           (getCurPerm m2', snd (getThreadR Htid'))).
        (* new memory is given by the self_simulation. *)
        exists m2', cd, f'. split; [|left].
        
        + (*Reestablish the concur_match *)
          simpl.
          move H0 at bottom.
          eapply Concur_update; eauto.
          econstructor 2; eauto.
          simpl in MATCH.
          unfold match_thread_target; simpl.
          constructor.
          exact MATCH.
        + (* Construct the step *)
          exists 0; simpl.
          do 2 eexists; split; [|reflexivity].
          replace m2' with (HybridMachineSig.diluteMem m2') by reflexivity.
          econstructor; eauto; simpl.
          econstructor; eauto.
          * simpl in *.
            eapply H0.
          * simpl. econstructor; eauto.
          * simpl; repeat (f_equal; try eapply Axioms.proof_irr).

            
      - (*  tid = hb*)
        pose proof (mtch_compiled _ _ _ _ _ _ H0 _ e Htid (contains12 H0 Htid)) as HH.
        destruct HH as (cd0 & H1 & ?).
        subst.

        (* This takes three styeps*)
        
        admit. (*Compiler case*)

        
      - (* tid > hb *)
        pose proof (mtch_source _ _ _ _ _ _ H0 _ l Htid (contains12 H0 Htid)) as HH.
        simpl in *.
        exploit_match.
        destroy_ev_step_sum; simpl in *.
        simpl.
        eapply (event_semantics.ev_step_ax1 (@semSem CSem)) in H2; eauto.
        replace Hcmpt with (memcompat1 cd mu st1 m1 st2 m2 H0) in H2
          by eapply Axioms.proof_irr.
        
        eapply Cself_simulation in H5; eauto.
        destruct H5 as (c2' & f' & t' & m2' & (CoreStep & MATCH & is_ext & inject_incr)).
        
        eapply (event_semantics.ev_step_ax2 (@semSem CSem)) in CoreStep.
        destruct CoreStep as (?&?); eauto.
         
        (* contains.*)
        pose proof (@contains12  _ _ _ _ _ _  H0 _ Htid) as Htid'.

        (* Construct the new thread pool *)
        exists (updThread Htid' (Krun (SState Clight.state Asm.state c2'))
           (getCurPerm m2', snd (getThreadR Htid'))).
        (* new memory is given by the self_simulation. *)
        exists m2', cd, f'. split; [|left].
        
        + (*Reestablish the concur_match *)
          simpl.
          move H0 at bottom.
          eapply Concur_update; eauto.
          econstructor 1; eauto.
          simpl in MATCH.
          unfold match_thread_source; simpl.
          constructor.
          exact MATCH.
        + (* Construct the step *)
          exists 0; simpl.
          do 2 eexists; split; [|reflexivity].
          replace m2' with (HybridMachineSig.diluteMem m2') by reflexivity.
          econstructor; eauto; simpl.
          econstructor; eauto.
          * simpl in *.
            eapply H0.
          * simpl. econstructor; eauto.
          * simpl; repeat (f_equal; try eapply Axioms.proof_irr).
    Admitted.

    Lemma machine_step_diagram:
          forall (m : option mem) (sge tge : HybridMachineSig.G) (U : list nat)
                 (tr : HybridMachineSig.event_trace) (st1 : ThreadPool (Some hb)) 
                 (m1 : mem) (U' : list nat) (tr' : HybridMachineSig.event_trace)
                 (st1' : ThreadPool (Some hb)) (m1' : mem),
            machine_semantics.machine_step (HybConcSem (Some hb) m) sge U tr st1 m1 U' tr' st1' m1' ->
            forall (cd : option compiler_index) (st2 : ThreadPool (Some (S hb))) 
                   (mu : meminj) (m2 : mem),
              concur_match cd mu st1 m1 st2 m2 ->
              exists
                (st2' : ThreadPool (Some (S hb))) (m2' : mem) (cd' : option compiler_index) 
                (mu' : meminj),
                concur_match cd' mu' st1' m1' st2' m2' /\
                machine_semantics.machine_step (HybConcSem (Some (S hb)) m) tge U tr st2 m2 U' tr' st2'
                                               m2'.
        Proof.
        Admitted.

        
        Lemma initial_diagram:
          forall (m : option mem) (s_mem s_mem' : mem) (main : val) (main_args : list val)
                 (s_mach_state : ThreadPool (Some hb)) (r1 : option res),
            machine_semantics.initial_machine (HybConcSem (Some hb) m) r1 s_mem s_mach_state s_mem'
                                              main main_args ->
            exists
              (j : meminj) (cd : option compiler_index) (t_mach_state : ThreadPool (Some (S hb))) 
              (t_mem t_mem' : mem) (r2 : option res),
              machine_semantics.initial_machine (HybConcSem (Some (S hb)) m) r2 t_mem t_mach_state
                                                t_mem' main main_args /\ concur_match cd j s_mach_state s_mem' t_mach_state t_mem'.
        Proof.
          intros m.
          
        simpl; unfold HybridMachineSig.init_machine''.
        intros ? ? ? ? ? ? (?&?).
        destruct r1; try solve[inversion H0].
        simpl in H0.
        destruct H0 as (init_thread&?&?); simpl in *.
        unfold initial_core_sum in *.
        destruct init_thread; destruct H0 as (LT&H0); simpl in LT.
        + admit. (*identical start!*)
        + admit. (*should follow from compiler simulation*)
        Admitted.
    
    Lemma compile_one_thread:
      forall m,
        HybridMachine_simulation_properties
          (HybConcSem (Some hb) m)
          (HybConcSem (Some (S hb)) m)
          (concur_match).
    Proof.
      intros.
      econstructor.
      - eapply option_wf.
        eapply (Injfsim_order_wf compiler_sim). (*well_founded order*)

      (*Initial Diagram*)
      - eapply initial_diagram.

      (* Internal Step diagram*)
      - eapply internal_step_diagram.

        (* Machine Step diagram *)
      - eapply machine_step_diagram.

      (* Halted *)
      - simpl; unfold HybridMachineSig.halted_machine; simpl; intros.
        destruct (HybridMachineSig.schedPeek U); inversion H0.
        eexists; reflexivity.

        (*Same running *)
      - eapply concur_match_same_running.
        
    Qed.

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
     ThreadPool (Some 0) -> Memory.Mem.mem -> ThreadPool None -> Memory.Mem.mem -> Prop.
 
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