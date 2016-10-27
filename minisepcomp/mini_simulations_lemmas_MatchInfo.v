Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Axioms.

Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import compcert.common.Events.
Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.
Require Import msl.Axioms.

Require Import sepcomp.mem_lemmas.
Require Import sepcomp.semantics.
Require Import sepcomp.semantics_lemmas.
Require Import sepcomp.effect_semantics. 
Require Import minisepcomp.mini_simulations_MatchInfo.

Require Import minisepcomp.BuiltinEffects.

(** * Simulations Lemmas *)

(** This file specializes [simulations] in a number of useful ways. *)

Section Eff_INJ_SIMU_DIAGRAMS.
  Context {F1 V1 C1 F2 V2 C2:Type}
          {Sem1 : @EffectSem (Genv.t F1 V1) C1} 
          {Sem2 : @EffectSem (Genv.t F2 V2) C2}

          {ge1: Genv.t F1 V1} 
          {ge2: Genv.t F2 V2}.
  Let core_data := C1.

  Variable match_states: core_data -> meminj ->  MatchInfo -> C1 -> mem ->  MatchInfo -> C2 -> mem -> Prop.
   
   (*Hypothesis genvs_dom_eq: genvs_domain_eq ge1 ge2.*)
   Hypothesis senvs_dom_eq : Senv.equiv ge1 ge2.

  (* Hypothesis ginfo_preserved : (*gvar_infos_eq ge1 ge2 /\*) findsymbols_preserved ge1 ge2.*)

   Hypothesis match_validblocks : 
    forall d j E1 c1 m1 E2 c2 m2 (MS: match_states d j E1 c1 m1 E2 c2 m2),
    meminj_valid j E1 E2 m1 m2.

   Hypothesis match_wd: 
    forall d j M1 L1 c1 m1 M2 L2 c2 m2 (MS: match_states d j (M1,L1) c1 m1 (M2,L2) c2 m2)
    b1 b2 d (J:j b1=Some(b2, d)), L1 b1 = L2 b2.

   Hypothesis match_genv:
    forall d j E1 c1 m1 E2 c2 m2 (MC : match_states d j E1 c1 m1 E2 c2 m2),
    symbols_inject j ge1 ge2 /\
    meminj_preserves_globals ge1 j /\
    (forall b, isGlobalBlock ge1 b = true -> j b <>None).

   Hypothesis inj_initial_cores:  
    forall v vals1 c1 m1 j vals2 m2,
    initial_core Sem1 ge1 v vals1 = Some c1 ->
    Mem.inject j m1 m2 -> 
    Forall2 (val_inject j) vals1 vals2 ->
    meminj_preserves_globals ge1 j -> symbols_inject j ge1 ge2 ->
    (*globalfunction_ptr_inject ge1 j -> MINI:MAYBE DON'T REMOVE THIS??*)
    mem_respects_readonly ge1 m1 -> mem_respects_readonly ge2 m2 ->
    exists c2, 
    initial_core Sem2 ge2 v vals2 = Some c2 
    /\ match_states c1 j EmptyInfo c1 m1 EmptyInfo c2 m2.

  Hypothesis inj_halted :
    forall cd j M1 L1 c1 m1 M2 L2 c2 m2 v1,
    match_states cd j (M1,L1) c1 m1 (M2,L2) c2 m2 ->
    halted Sem1 c1 = Some v1 ->
    exists v2, 
    Mem.inject j m1 m2 
    /\ mem_respects_readonly ge1 m1 /\ mem_respects_readonly ge2 m2
    /\ val_inject j v1 v2 
    /\ halted Sem2 c2 = Some v2 
    /\ EffectsPropagate j M1 M2.

  Hypothesis inj_at_external : 
    forall cd j M1 L1 c1 m1 M2 L2 c2 m2 e vals1 efsig,
    match_states cd j (M1,L1) c1 m1 (M2,L2) c2 m2 ->
    at_external Sem1 c1 = Some (e,efsig,vals1) ->
    Mem.inject j m1 m2 
    /\ mem_respects_readonly ge1 m1 /\ mem_respects_readonly ge2 m2
    /\ EffectsPropagate j M1 M2
    /\ exists vals2, 
       Forall2 (val_inject j) vals1 vals2 
       /\ at_external Sem2 c2 = Some (e,efsig,vals2).

Section EFF_INJ_SIMULATION_STAR_WF.
Variable order: C1 -> C1 -> Prop.
Hypothesis order_wf: well_founded order.

  Hypothesis inj_after_external:
    forall cd j M1 L1 st1 M2 L2 st2 m1 e vals1 m2 efsig vals2 e' efsig'
      (MemInjMu: Mem.inject j m1 m2)
      (MatchMu: match_states cd j (M1,L1) st1 m1 (M2,L2) st2 m2)
      (AtExtSrc: at_external Sem1 st1 = Some (e,efsig,vals1))

      (AtExtTgt: at_external Sem2 st2 = Some (e',efsig',vals2)) 
      (ValInjMu: Forall2 (val_inject j) vals1 vals2),

      forall j' ret1 m1' ret2 m2'
        (INC: mini_extern_incr j j' L1 L2) 
        (GSep: globals_separate m1 ge2 j j')
        (MV: meminj_valid j' (M1,L1)(M2,L2) m1' m2')

        (MemInjNu': Mem.inject j' m1' m2')
        (RValInjNu': val_inject j' ret1 ret2)

        (FwdSrc: mem_forward m1 m1') (FwdTgt: mem_forward m2 m2')
        (RDO1: RDOnly_fwd m1 m1' (ReadOnlyBlocks ge1))
        (RDO2: RDOnly_fwd m2 m2' (ReadOnlyBlocks ge2))

        (UnchSrc: Mem.unchanged_on (fun b1 ofs => L1 b1 = true /\ j b1 = None) m1 m1')
        (UnchTgt: Mem.unchanged_on (o_o_reach j L2 m1) m2 m2') ,

        exists st1', exists st2',
          after_external Sem1 (Some ret1) st1 = Some st1' /\
          after_external Sem2 (Some ret2) st2 = Some st2' /\
          match_states st1' j' (M1,L1) st1' m1' (M2,L2) st2' m2'.

  Hypothesis inj_effcore_diagram : 
    forall st1 m1 st1' m1' U1, 
    effstep Sem1 ge1 U1 st1 m1 st1' m1' ->
    forall st2 j m2 E1 E2,
    match_states st1 j E1 st1 m1 E2 st2 m2 ->
    exists st2', exists m2', exists j', exists U2,              
      ((effstep_plus Sem2 ge2 U2 st2 m2 st2' m2' \/
       (effstep_star Sem2 ge2 U2 st2 m2 st2' m2' /\ order st1' st1)) /\
       match E1, E2 with (M1,L1), (M2, L2) =>
         let L1' := (fun b : block => L1 b || freshblock m1 m1' b) in
         let L2' := (fun b : block => L2 b || freshblock m2 m2' b) in
         let M1' := (fun b z => valid_block_dec m1 b && negb (L1 b) && (M1 b z || U1 b z)) in
         let M2' := (fun b z => valid_block_dec m2 b && negb (L2 b) && (M2 b z || U2 b z)) in
         mini_intern_incr j j' L1' L2'
      /\ globals_separate m1 ge2 j j' 
(*      /\ mini_locally_allocated L1 L2 m1 m2 L1' L2' m1' m2' *)
      /\ match_states st1' j' (M1',L1') st1' m1' (M2',L2') st2' m2'
       end).

Lemma  inj_simulation_star_wf: 
  Mini_simulation_inj.Mini_simulation_inject Sem1 Sem2 ge1 ge2.
Proof.
  eapply Mini_simulation_inj.Build_Mini_simulation_inject with
    (core_ord := order)
    (match_state := fun d j E1 c1 m1 E2 c2 m2 => d = c1 /\ 
                     match_states d j E1 c1 m1 E2 c2 m2).
+ apply order_wf.
+ clear - match_wd. intros. destruct MS; subst; eauto.
+ assumption.
(*clear - sinfo_preserved. assumption.*)
+ clear - match_genv. intros. destruct MC; subst. eauto.
+ clear - match_validblocks. intros. destruct MS; subst. eauto.
+ clear - inj_initial_cores. intros.
  exploit inj_initial_cores; try eassumption; intros [c2 [INI MS]].
  exists c1, c2. intuition. 
+ clear - inj_effcore_diagram senvs_dom_eq.
  intros. destruct H0; subst.
  exploit inj_effcore_diagram; try eassumption. 
  intros [c2' [m2' [j' [U2' [STEP2 PROP]]]]]. 
  exists c2', m2', st1', j', U2'. 
  split; try assumption.
  destruct E1 as [M1 L1]. destruct E2 as [M2 L2].
  destruct PROP as [IINC [GSEP MATCH]].
  split; try assumption.
  split; try assumption.
  split; trivial. 
+ clear - inj_halted. intros. destruct H; subst.
  exploit inj_halted; try eassumption. intros [v2 [INJ [VAL HH]]].
  exists v2; intuition.
+ clear - inj_at_external. intros. destruct H; subst.
  exploit inj_at_external; try eassumption.
  intros [INJ [MRR1 [MRR2 [Propgt [vals2 [VALS AtExt2]]]]]].
  intuition. exists vals2. split; trivial. 
+ clear - inj_after_external. intros. 
  destruct MatchMu as [ZZ matchMu]. subst cd.
  specialize (inj_after_external st1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 
      MemInjMu matchMu AtExtSrc AtExtTgt ValInjMu).
  exploit (inj_after_external j' ret1 m1' ret2 m2'); try assumption.
  intros [st1' [st2' [AftExt1 [AftExt2 MS']]]]; try eassumption.
  exists st1', st1', st2'. intuition.
Qed.

End EFF_INJ_SIMULATION_STAR_WF.

Section EFF_INJ_SIMULATION_STAR_WF_TYPED.
Variable order: C1 -> C1 -> Prop.
Hypothesis order_wf: well_founded order.

  Hypothesis inj_after_external:
    forall cd j M1 L1 st1 M2 L2 st2 m1 e vals1 m2 efsig vals2 e' efsig'
      (MemInjMu: Mem.inject j m1 m2)
      (MatchMu: match_states cd j (M1,L1) st1 m1 (M2,L2) st2 m2)
      (AtExtSrc: at_external Sem1 st1 = Some (e,efsig,vals1))

      (AtExtTgt: at_external Sem2 st2 = Some (e',efsig',vals2)) 
      (ValInjMu: Forall2 (val_inject j) vals1 vals2),

      forall j' ret1 m1' ret2 m2'
        (HasTy1: Val.has_type ret1 (proj_sig_res efsig))
        (HasTy2: Val.has_type ret2 (proj_sig_res efsig'))
        (INC: mini_extern_incr j j' L1 L2) 
        (GSep: globals_separate m1 ge2 j j')

        (MV: meminj_valid j' (M1,L1) (M2,L2) m1' m2')

        (MemInjNu': Mem.inject j' m1' m2')
        (RValInjNu': val_inject j' ret1 ret2)

        (FwdSrc: mem_forward m1 m1') (FwdTgt: mem_forward m2 m2')
        (RDO1: RDOnly_fwd m1 m1' (ReadOnlyBlocks ge1))
        (RDO2: RDOnly_fwd m2 m2' (ReadOnlyBlocks ge2))

        (UnchSrc: Mem.unchanged_on (fun b1 ofs => L1 b1 = true /\ j b1 = None) m1 m1')
        (UnchTgt: Mem.unchanged_on (o_o_reach j L2 m1) m2 m2') ,

        exists st1', exists st2',
          after_external Sem1 (Some ret1) st1 = Some st1' /\
          after_external Sem2 (Some ret2) st2 = Some st2' /\
          match_states st1' j' (M1,L1) st1' m1' (M2,L2) st2' m2'.

  Hypothesis inj_effcore_diagram : 
    forall st1 m1 st1' m1' U1, 
    effstep Sem1 ge1 U1 st1 m1 st1' m1' ->
    forall st2 j m2 E1 E2,
    match_states st1 j E1 st1 m1 E2 st2 m2 ->
    exists st2' m2' j' U2,              
      ((effstep_plus Sem2 ge2 U2 st2 m2 st2' m2' \/
       (effstep_star Sem2 ge2 U2 st2 m2 st2' m2' /\ order st1' st1)) /\
       match E1, E2 with (M1,L1), (M2, L2) =>
         let L1' := (fun b : block => L1 b || freshblock m1 m1' b) in
         let L2' := (fun b : block => L2 b || freshblock m2 m2' b) in
         let M1' := (fun b z => valid_block_dec m1 b && negb (L1 b) && (M1 b z || U1 b z)) in
         let M2' := (fun b z => valid_block_dec m2 b && negb (L2 b) && (M2 b z || U2 b z)) in
         mini_intern_incr j j' L1' L2'
      /\ globals_separate m1 ge2 j j' 
(*      /\ mini_locally_allocated L1 L2 m1 m2 L1' L2' m1' m2' *)
      /\ match_states st1' j' (M1',L1') st1' m1' (M2',L2') st2' m2'
       end).

Lemma inj_simulation_star_wf_typed: 
  Mini_simulation_inj.Mini_simulation_inject Sem1 Sem2 ge1 ge2.
Proof.
  eapply Mini_simulation_inj.Build_Mini_simulation_inject with
    (core_ord := order)
    (match_state := fun d j L1 c1 m1 L2 c2 m2 => d = c1 /\ match_states d j L1 c1 m1 L2 c2 m2).
+ apply order_wf.
+ clear - match_wd. intros. destruct MS; subst; eauto.
+ assumption.
(*clear - ginfo_preserved. assumption.*)
+ clear - match_genv. intros. destruct MC; subst. eauto.
+ clear - match_validblocks. intros. destruct MS; subst. eauto.
+ clear - inj_initial_cores. intros.
  exploit inj_initial_cores; try eassumption; intros [c2 [INI MS]].
  exists c1, c2. intuition.  
+ clear - inj_effcore_diagram senvs_dom_eq. 
  intros. destruct H0; subst.
  exploit inj_effcore_diagram; try eassumption.
  intros [c2' [m2' [j' [U2 [STEP' PROP]]]]]. 
  exists c2', m2', st1', j', U2. 
  split; try assumption.
  destruct E1 as [M1 L1]. destruct E2 as [M2 L2]. destruct PROP as [INC [GSEP MATCH]].
  split; try assumption.
  split; try assumption.
(*  split. eapply gsep_domain_eq; eassumption.*)
  split; trivial. 
+ clear - inj_halted. intros. destruct H; subst.
  exploit inj_halted; try eassumption. intros [v2 [INJ [VAL HH]]].
  exists v2; intuition.
+ clear - inj_at_external. intros. destruct H; subst.
  exploit inj_at_external; try eassumption.
  intros [INJ [MRR1 [MRR2 [EPROP [vals2 [VALS AtExt2]]]]]].
  intuition. exists vals2. split; trivial. 
+ clear - inj_after_external. intros. 
  destruct MatchMu as [ZZ matchMu]. subst cd.
  specialize (inj_after_external st1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 
      MemInjMu matchMu AtExtSrc AtExtTgt ValInjMu).
  exploit (inj_after_external j' _ m1' _ m2' HasTy1 HasTy2); try assumption.
  intros [st1' [st2' [AftExt1 [AftExt2 MS']]]]; try eassumption.
  exists st1', st1', st2'. intuition.
Qed.

End EFF_INJ_SIMULATION_STAR_WF_TYPED.

Section EFF_INJ_SIMULATION_STAR.
  Variable measure: C1 -> nat.

  Hypothesis inj_after_external:
    forall cd j M1 L1 st1 M2 L2 st2 m1 e vals1 m2 efsig vals2 e' efsig'
      (MemInjMu: Mem.inject j m1 m2)
      (MatchMu: match_states cd j (M1,L1) st1 m1 (M2,L2) st2 m2)
      (AtExtSrc: at_external Sem1 st1 = Some (e,efsig,vals1))

      (AtExtTgt: at_external Sem2 st2 = Some (e',efsig',vals2)) 
      (ValInjMu: Forall2 (val_inject j) vals1 vals2),

      forall j' ret1 m1' ret2 m2'
        (INC: mini_extern_incr j j' L1 L2) 
        (GSep: globals_separate m1 ge2 j j')

        (MV: meminj_valid j' (M1,L1) (M2,L2) m1' m2')

        (MemInjNu': Mem.inject j' m1' m2')
        (RValInjNu': val_inject j' ret1 ret2)

        (FwdSrc: mem_forward m1 m1') (FwdTgt: mem_forward m2 m2')
        (RDO1: RDOnly_fwd m1 m1' (ReadOnlyBlocks ge1))
        (RDO2: RDOnly_fwd m2 m2' (ReadOnlyBlocks ge2))

        (UnchSrc: Mem.unchanged_on (fun b1 ofs => L1 b1 = true /\ j b1 = None) m1 m1')
        (UnchTgt: Mem.unchanged_on (o_o_reach j L2 m1) m2 m2') ,

        exists st1', exists st2',
          after_external Sem1 (Some ret1) st1 = Some st1' /\
          after_external Sem2 (Some ret2) st2 = Some st2' /\
          match_states st1' j' (M1,L1) st1' m1' (M2,L2) st2' m2'.

  Hypothesis inj_effcore_diagram : 
    forall st1 m1 st1' m1' U1, 
    effstep Sem1 ge1 U1 st1 m1 st1' m1' ->
    forall st2 j m2 E1 E2,
    match_states st1 j E1 st1 m1 E2 st2 m2 ->
    exists st2' m2' j' U2,                
            (effstep_plus Sem2 ge2 U2 st2 m2 st2' m2' \/
             ((measure st1' < measure st1)%nat /\ effstep_star Sem2 ge2 U2 st2 m2 st2' m2'))  
     /\ match E1, E2 with (M1,L1), (M2, L2) =>
         let L1' := (fun b : block => L1 b || freshblock m1 m1' b) in
         let L2' := (fun b : block => L2 b || freshblock m2 m2' b) in
         let M1' := (fun b z => valid_block_dec m1 b && negb (L1 b) && (M1 b z || U1 b z)) in
         let M2' := (fun b z => valid_block_dec m2 b && negb (L2 b) && (M2 b z || U2 b z)) in
         mini_intern_incr j j' L1' L2'
      /\ globals_separate m1 ge2 j j' 
(*      /\ mini_locally_allocated L1 L2 m1 m2 L1' L2' m1' m2' *)
      /\ match_states st1' j' (M1',L1') st1' m1' (M2',L2') st2' m2'
       end.

Lemma inj_simulation_star: 
  Mini_simulation_inj.Mini_simulation_inject Sem1 Sem2 ge1 ge2.
Proof.
  eapply inj_simulation_star_wf.
+ apply  (well_founded_ltof _ measure).
+ apply inj_after_external.
+ clear - inj_effcore_diagram senvs_dom_eq. intros.
  exploit inj_effcore_diagram; try eassumption.
   intros [c2' [m2' [j' [U2 [STEP' PROP]]]]].
  exists c2'. exists m2'. exists j', U2. 
  destruct E1 as [M1 L1]. destruct E2 as [M2 L2]. destruct PROP as [INC [GSEP MATCH]].
  split. intuition.
  split; try assumption.
  split; try assumption.
  (*split. eapply globalsep_domain_eq. eassumption.*)
Qed.

End EFF_INJ_SIMULATION_STAR.

Section EFF_INJ_SIMULATION_STAR_TYPED.
  Variable measure: C1 -> nat.

  Hypothesis inj_after_external:
    forall cd j M1 L1 st1 M2 L2 st2 m1 e vals1 m2 efsig vals2 e' efsig'
      (MemInjMu: Mem.inject j m1 m2)
      (MatchMu: match_states cd j (M1,L1) st1 m1 (M2,L2) st2 m2)
      (AtExtSrc: at_external Sem1 st1 = Some (e,efsig,vals1))

      (AtExtTgt: at_external Sem2 st2 = Some (e',efsig',vals2)) 
      (ValInjMu: Forall2 (val_inject j) vals1 vals2),

      forall j' ret1 m1' ret2 m2'
        (HasTy1: Val.has_type ret1 (proj_sig_res efsig))
        (HasTy2: Val.has_type ret2 (proj_sig_res efsig'))
        (INC: mini_extern_incr j j' L1 L2) 
        (GSep: globals_separate m1 ge2 j j')

        (MV: meminj_valid j' (M1,L1) (M2,L2) m1' m2')

        (MemInjNu': Mem.inject j' m1' m2')
        (RValInjNu': val_inject j' ret1 ret2)

        (FwdSrc: mem_forward m1 m1') (FwdTgt: mem_forward m2 m2')
        (RDO1: RDOnly_fwd m1 m1' (ReadOnlyBlocks ge1))
        (RDO2: RDOnly_fwd m2 m2' (ReadOnlyBlocks ge2))

        (UnchSrc: Mem.unchanged_on (fun b1 ofs => L1 b1 = true /\ j b1 = None) m1 m1')
        (UnchTgt: Mem.unchanged_on (o_o_reach j L2 m1) m2 m2') ,

        exists st1', exists st2',
          after_external Sem1 (Some ret1) st1 = Some st1' /\
          after_external Sem2 (Some ret2) st2 = Some st2' /\
          match_states st1' j' (M1,L1) st1' m1' (M2,L2) st2' m2'.

  Hypothesis inj_effcore_diagram : 
    forall st1 m1 st1' m1' U1, 
    effstep Sem1 ge1 U1 st1 m1 st1' m1' ->
    forall st2 j m2 E1 E2,
    match_states st1 j E1 st1 m1 E2 st2 m2 ->
    exists st2', exists m2', exists j', exists U2,            
            (effstep_plus Sem2 ge2 U2 st2 m2 st2' m2' \/
             ((measure st1' < measure st1)%nat /\ effstep_star Sem2 ge2 U2 st2 m2 st2' m2'))
     /\ match E1, E2 with (M1,L1), (M2, L2) =>
         let L1' := (fun b : block => L1 b || freshblock m1 m1' b) in
         let L2' := (fun b : block => L2 b || freshblock m2 m2' b) in
         let M1' := (fun b z => valid_block_dec m1 b && negb (L1 b) && (M1 b z || U1 b z)) in
         let M2' := (fun b z => valid_block_dec m2 b && negb (L2 b) && (M2 b z || U2 b z)) in
         mini_intern_incr j j' L1' L2'
      /\ globals_separate m1 ge2 j j' 
(*      /\ mini_locally_allocated L1 L2 m1 m2 L1' L2' m1' m2' *)
      /\ match_states st1' j' (M1',L1') st1' m1' (M2',L2') st2' m2'
       end.

Lemma inj_simulation_star_typed: 
  Mini_simulation_inj.Mini_simulation_inject Sem1 Sem2 ge1 ge2.
Proof.
  eapply inj_simulation_star_wf_typed.
+ apply  (well_founded_ltof _ measure).
+ intros. eapply inj_after_external with (j := j); eauto.
+ clear - inj_effcore_diagram. intros.
  exploit inj_effcore_diagram; try eassumption.
    intros [c2' [m2' [j' [U2 [STEP' PROP]]]]].
  exists c2'. exists m2'. exists j', U2. 
  destruct E1 as [M1 L1]. destruct E2 as [M2 L2]. destruct PROP as [INC [GSEP MATCH]].
  split. intuition.
  split; try assumption.
  split; try assumption.
  (*split. eapply globalsep_domain_eq. eassumption.*)
Qed.

End EFF_INJ_SIMULATION_STAR_TYPED.

Section EFF_INJ_SIMULATION_PLUS.
  Variable measure: C1 -> nat.
  Hypothesis inj_after_external:
    forall cd j M1 L1 st1 M2 L2 st2 m1 e vals1 m2 efsig vals2 e' efsig'
      (MemInjMu: Mem.inject j m1 m2)
      (MatchMu: match_states cd j (M1,L1) st1 m1 (M2,L2) st2 m2)
      (AtExtSrc: at_external Sem1 st1 = Some (e,efsig,vals1))

      (AtExtTgt: at_external Sem2 st2 = Some (e',efsig',vals2)) 
      (ValInjMu: Forall2 (val_inject j) vals1 vals2),

      forall j' ret1 m1' ret2 m2'
        (INC: mini_extern_incr j j' L1 L2) 
        (GSep: globals_separate m1 ge2 j j')

       (MV: meminj_valid j' (M1,L1) (M2,L2) m1' m2')

        (MemInjNu': Mem.inject j' m1' m2')
        (RValInjNu': val_inject j' ret1 ret2)

        (FwdSrc: mem_forward m1 m1') (FwdTgt: mem_forward m2 m2')
        (RDO1: RDOnly_fwd m1 m1' (ReadOnlyBlocks ge1))
        (RDO2: RDOnly_fwd m2 m2' (ReadOnlyBlocks ge2))

        (UnchSrc: Mem.unchanged_on (fun b1 ofs => L1 b1 = true /\ j b1 = None) m1 m1')
        (UnchTgt: Mem.unchanged_on (o_o_reach j L2 m1) m2 m2') ,

        exists st1', exists st2',
          after_external Sem1 (Some ret1) st1 = Some st1' /\
          after_external Sem2 (Some ret2) st2 = Some st2' /\
          match_states st1' j' (M1,L1) st1' m1' (M2,L2) st2' m2'.

  Hypothesis inj_effcore_diagram : 
    forall st1 m1 st1' m1' U1, 
    effstep Sem1 ge1 U1 st1 m1 st1' m1' ->
    forall st2 j m2 E1 E2,
    match_states st1 j E1 st1 m1 E2 st2 m2 ->
    exists st2', exists m2', exists j', exists U2,              
            (effstep_plus Sem2 ge2 U2 st2 m2 st2' m2' \/
             ((measure st1' < measure st1)%nat /\ effstep_star Sem2 ge2 U2 st2 m2 st2' m2'))
            /\ match E1, E2 with (M1,L1), (M2, L2) =>
         let L1' := (fun b : block => L1 b || freshblock m1 m1' b) in
         let L2' := (fun b : block => L2 b || freshblock m2 m2' b) in
         let M1' := (fun b z => valid_block_dec m1 b && negb (L1 b) && (M1 b z || U1 b z)) in
         let M2' := (fun b z => valid_block_dec m2 b && negb (L2 b) && (M2 b z || U2 b z)) in
         mini_intern_incr j j' L1' L2'
      /\ globals_separate m1 ge2 j j' 
(*      /\ mini_locally_allocated L1 L2 m1 m2 L1' L2' m1' m2' *)
      /\ match_states st1' j' (M1',L1') st1' m1' (M2',L2') st2' m2'
       end.

Lemma inj_simulation_plus: 
  Mini_simulation_inj.Mini_simulation_inject Sem1 Sem2 ge1 ge2.
Proof.
  apply inj_simulation_star with (measure:=measure); auto.
Qed.

End EFF_INJ_SIMULATION_PLUS.

Section EFF_INJ_SIMULATION_PLUS_TYPED.
  Variable measure: C1 -> nat.

  Hypothesis inj_after_external:
    forall cd j M1 L1 st1 M2 L2 st2 m1 e vals1 m2 efsig vals2 e' efsig'
      (MemInjMu: Mem.inject j m1 m2)
      (MatchMu: match_states cd j (M1,L1) st1 m1 (M2,L2) st2 m2)
      (AtExtSrc: at_external Sem1 st1 = Some (e,efsig,vals1))

      (AtExtTgt: at_external Sem2 st2 = Some (e',efsig',vals2)) 
      (ValInjMu: Forall2 (val_inject j) vals1 vals2),

      forall j' ret1 m1' ret2 m2'
        (HasTy1: Val.has_type ret1 (proj_sig_res efsig))
        (HasTy2: Val.has_type ret2 (proj_sig_res efsig'))
        (INC: mini_extern_incr j j' L1 L2) 
        (GSep: globals_separate m1 ge2 j j')

        (MV: meminj_valid j' (M1,L1) (M2,L2) m1' m2')

        (MemInjNu': Mem.inject j' m1' m2')
        (RValInjNu': val_inject j' ret1 ret2)

        (FwdSrc: mem_forward m1 m1') (FwdTgt: mem_forward m2 m2')
        (RDO1: RDOnly_fwd m1 m1' (ReadOnlyBlocks ge1))
        (RDO2: RDOnly_fwd m2 m2' (ReadOnlyBlocks ge2))

        (UnchSrc: Mem.unchanged_on (fun b1 ofs => L1 b1 = true /\ j b1 = None) m1 m1')
        (UnchTgt: Mem.unchanged_on (o_o_reach j L2 m1) m2 m2') ,

        exists st1', exists st2',
          after_external Sem1 (Some ret1) st1 = Some st1' /\
          after_external Sem2 (Some ret2) st2 = Some st2' /\
          match_states st1' j' (M1,L1) st1' m1' (M2,L2) st2' m2'.

  Hypothesis inj_effcore_diagram : 
    forall st1 m1 st1' m1' U1, 
    effstep Sem1 ge1 U1 st1 m1 st1' m1' ->
    forall st2 j m2 E1 E2,
    match_states st1 j E1 st1 m1 E2 st2 m2 ->
    exists st2', exists m2', exists j', exists U2,                 
            (effstep_plus Sem2 ge2 U2 st2 m2 st2' m2' \/
             ((measure st1' < measure st1)%nat /\ effstep_star Sem2 ge2 U2 st2 m2 st2' m2'))
            /\  match E1, E2 with (M1,L1), (M2, L2) =>
         let L1' := (fun b : block => L1 b || freshblock m1 m1' b) in
         let L2' := (fun b : block => L2 b || freshblock m2 m2' b) in
         let M1' := (fun b z => valid_block_dec m1 b && negb (L1 b) && (M1 b z || U1 b z)) in
         let M2' := (fun b z => valid_block_dec m2 b && negb (L2 b) && (M2 b z || U2 b z)) in
         mini_intern_incr j j' L1' L2'
      /\ globals_separate m1 ge2 j j' 
(*      /\ mini_locally_allocated L1 L2 m1 m2 L1' L2' m1' m2' *)
      /\ match_states st1' j' (M1',L1') st1' m1' (M2',L2') st2' m2'
       end. 

Lemma inj_simulation_plus_typed: 
  Mini_simulation_inj.Mini_simulation_inject Sem1 Sem2 ge1 ge2.
Proof.
  apply inj_simulation_star_typed with (measure:=measure); auto.
Qed.

End EFF_INJ_SIMULATION_PLUS_TYPED.

End Eff_INJ_SIMU_DIAGRAMS.

Lemma freshblockProp_char m m' b: freshblock m m' b = true <-> freshblockProp m m' b.
Proof. rewrite freshblock_asProp. reflexivity. Qed.

Lemma freshblockProp_charF: forall m m' b, 
      (~freshblockProp m m' b) <-> (Mem.valid_block m b \/ ~Mem.valid_block m' b).
Proof. intros.
  unfold freshblockProp. 
  remember (valid_block_dec m' b) as s'; destruct s'; simpl; clear Heqs'. 
  + remember (valid_block_dec m b) as s; destruct s; simpl; clear Heqs; intuition.
  + intuition.
Qed.

Lemma freshblockProp_irrefl: forall m b, ~ freshblockProp m m b.
Proof. intros. apply freshblockProp_charF.
  destruct (valid_block_dec m b).
  left; trivial. right; trivial.
Qed.

Lemma freshblockProp_trans: forall m m'' m' 
     (FWD: mem_forward m m'') (FWD': mem_forward m'' m') b,
     (freshblockProp m m'' b \/ freshblockProp m'' m' b) = freshblockProp m m' b.
Proof. intros. apply prop_ext. split; intros.
+ destruct H as [[H1 H2] | [H1 H2]]. split; trivial. apply FWD'; trivial.
  split; trivial. intros N. apply H2; clear H2. apply FWD; trivial.
+ destruct H.
  destruct (valid_block_dec m'' b).
  - left; split; trivial.
  - right; split; trivial.
Qed.

Lemma freshblock_charF: forall m m' b, 
      (freshblock m m' b = false) <-> (Mem.valid_block m b \/ ~Mem.valid_block m' b).
Proof. intros.
  unfold freshblock. 
  remember (valid_block_dec m' b) as s'; destruct s'; simpl; clear Heqs'. 
  + remember (valid_block_dec m b) as s; destruct s; simpl; clear Heqs; intuition.
  + intuition.
Qed.

Lemma freshblock_freshblockProp m m' b: freshblock m m' b = true <-> freshblockProp m m' b.
Proof. rewrite freshblock_asProp. reflexivity. Qed.

Lemma freshblock_irrefl: forall m b, freshblock m m b = false.
Proof. intros. apply freshblock_charF.
  destruct (valid_block_dec m b).
  left; trivial. right; trivial.
Qed.

Lemma freshblock_trans: forall m m'' m' 
     (FWD: mem_forward m m'') (FWD': mem_forward m'' m') b,
     (freshblock m m'' b || freshblock m'' m' b) = freshblock m m' b.
Proof. intros.
  remember (freshblock m m' b) as d.
  destruct d; unfold freshblock in *.
  + destruct (valid_block_dec m' b); simpl in *; try discriminate.
    destruct (valid_block_dec m b); simpl in *; try discriminate.
    destruct (valid_block_dec m'' b); trivial.
  + destruct (valid_block_dec m' b); simpl in *.
    - destruct (valid_block_dec m b); simpl in *; try discriminate.
      destruct (valid_block_dec m'' b); simpl; trivial.
      elim n. apply FWD; trivial.
    - rewrite orb_false_r. 
      destruct (valid_block_dec m b); simpl in *.
      destruct (valid_block_dec m'' b); simpl; trivial.
      destruct (valid_block_dec m'' b); simpl; trivial.
      elim n. apply FWD'; trivial.
Qed.

Definition full_comp (j1 j2: meminj) :=
  forall b0 b1 delta1, j1 b0 = Some (b1, delta1) -> exists b2 delta2, j2 b1 = Some (b2, delta2).

Definition full_ext (j1 j2: meminj) L1 L2:=
  forall b1 b2 delta1, L1 b1 = false -> j1 b1 = Some (b2, delta1) -> 
  (L2 b2 = false /\ exists b3 delta2, j2 b2 = Some (b3, delta2)).


(*
Definition compose_sm (mu1 mu2 : SM_Injection) : SM_Injection :=
 Build_SM_Injection 
   (locBlocksSrc mu1) (locBlocksTgt mu2)
   (pubBlocksSrc mu1) (pubBlocksTgt mu2)
   (compose_meminj (local_of mu1) (local_of mu2))
   (extBlocksSrc mu1) (extBlocksTgt mu2)
   (frgnBlocksSrc mu1) (frgnBlocksTgt mu2) 
   (compose_meminj (extern_of mu1) (extern_of mu2)).

Lemma compose_sm_valid: forall mu1 mu2 m1 m2 m2' m3
          (SMV1: sm_valid mu1 m1 m2) (SMV2: sm_valid mu2 m2' m3),
       sm_valid (compose_sm mu1 mu2) m1 m3.
Proof.  split. apply SMV1. apply SMV2. Qed.

Lemma compose_sm_pub: forall mu12 mu23 
         (HypPub: forall b, pubBlocksTgt mu12 b = true ->
                            pubBlocksSrc mu23 b = true)
         (WD1:SM_wd mu12),
      pub_of (compose_sm mu12 mu23) =
      compose_meminj (pub_of mu12) (pub_of mu23).
Proof. intros. unfold compose_sm, pub_of. 
  extensionality b. 
  destruct mu12 as [locBSrc1 locBTgt1 pSrc1 pTgt1 local1 extBSrc1 extBTgt1 fSrc1 fTgt1 extern1]; simpl.
  destruct mu23 as [locBSrc2 locBTgt2 pSrc2 pTgt2 local2 extBSrc2 extBTgt2 fSrc2 fTgt2 extern2]; simpl.
  remember (pSrc1 b) as d; destruct d; apply eq_sym in Heqd.
    destruct (pubSrc _ WD1 _ Heqd) as [b2 [d1 [LOC1 Tgt1]]]; simpl in *.
    rewrite Heqd in LOC1. apply HypPub in Tgt1. 
    unfold compose_meminj. rewrite Heqd. rewrite LOC1. rewrite Tgt1.
    trivial.
  unfold compose_meminj.
    rewrite Heqd. trivial.
Qed.

Lemma compose_sm_DomSrc: forall mu12 mu23,
  DomSrc (compose_sm mu12 mu23) = DomSrc mu12.
Proof. intros. unfold compose_sm, DomSrc; simpl. trivial. Qed. 

Lemma compose_sm_DomTgt: forall mu12 mu23,
  DomTgt (compose_sm mu12 mu23) = DomTgt mu23.
Proof. intros. unfold compose_sm, DomTgt; simpl. trivial. Qed. 

Lemma compose_sm_foreign: forall mu12 mu23
         (HypFrg: forall b, frgnBlocksTgt mu12 b = true ->
                            frgnBlocksSrc mu23 b = true)
         (WD1:SM_wd mu12),
      foreign_of (compose_sm mu12 mu23) = 
      compose_meminj (foreign_of mu12) (foreign_of mu23).
Proof. intros. unfold compose_sm, foreign_of. 
  extensionality b. 
  destruct mu12 as [locBSrc1 locBTgt1 pSrc1 pTgt1 local1 extBSrc1 extBTgt1 fSrc1 fTgt1 extern1]; simpl.
  destruct mu23 as [locBSrc2 locBTgt2 pSrc2 pTgt2 local2 extBSrc2 extBTgt2 fSrc2 fTgt2 extern2]; simpl.
  remember (fSrc1 b) as d; destruct d; apply eq_sym in Heqd.
    destruct (frgnSrc _ WD1 _ Heqd) as [b2 [d1 [EXT1 Tgt1]]]; simpl in *.
    rewrite Heqd in EXT1. apply HypFrg in Tgt1. 
    unfold compose_meminj. rewrite Heqd. rewrite EXT1. rewrite Tgt1.
    trivial.
  unfold compose_meminj.
    rewrite Heqd. trivial.
Qed.

Lemma compose_sm_priv: forall mu12 mu23,
   priv_of (compose_sm mu12 mu23) =
   compose_meminj (priv_of mu12) (local_of mu23).
Proof. intros. unfold priv_of, compose_sm.
  extensionality b.
  destruct mu12 as [locBSrc1 locBTgt1 pSrc1 pTgt1 local1 extBSrc1 extBTgt1 fSrc1 fTgt1 extern1]; simpl.
  destruct mu23 as [locBSrc2 locBTgt2 pSrc2 pTgt2 local2 extBSrc2 extBTgt2 fSrc2 fTgt2 extern2]; simpl.
  remember (pSrc1 b) as d; destruct d; apply eq_sym in Heqd.
    unfold compose_meminj. rewrite Heqd. trivial.
  unfold compose_meminj.
    rewrite Heqd. trivial.
Qed.

Lemma compose_sm_unknown: forall mu12 mu23,
   unknown_of (compose_sm mu12 mu23) = 
   compose_meminj (unknown_of mu12) (extern_of mu23).
Proof. intros. unfold unknown_of, compose_sm.
  extensionality b.
  destruct mu12 as [locBSrc1 locBTgt1 pSrc1 pTgt1 local1 extBSrc1 extBTgt1 fSrc1 fTgt1 extern1]; simpl.
  destruct mu23 as [locBSrc2 locBTgt2 pSrc2 pTgt2 local2 extBSrc2 extBTgt2 fSrc2 fTgt2 extern2]; simpl.
  remember (locBSrc1 b) as d; destruct d; apply eq_sym in Heqd.
    unfold compose_meminj. rewrite Heqd. trivial.
  remember (fSrc1 b) as q; destruct q; apply eq_sym in Heqq.
    unfold compose_meminj. rewrite Heqd. rewrite Heqq. trivial.
  unfold compose_meminj.
    rewrite Heqd. rewrite Heqq. trivial.
Qed.

Lemma compose_sm_local: forall mu12 mu23,
   local_of (compose_sm mu12 mu23) =
   compose_meminj (local_of mu12) (local_of mu23).
Proof. intros. reflexivity. Qed. 

Lemma compose_sm_extern: forall mu12 mu23,
   extern_of (compose_sm mu12 mu23) =
   compose_meminj (extern_of mu12) (extern_of mu23).
Proof. intros. reflexivity. Qed. 

Lemma compose_sm_shared: forall mu12 mu23 
         (HypPub: forall b, pubBlocksTgt mu12 b = true ->
                            pubBlocksSrc mu23 b = true)
         (HypFrg: forall b, frgnBlocksTgt mu12 b = true ->
                            frgnBlocksSrc mu23 b = true)
         (WD1:SM_wd mu12) (WD2:SM_wd mu23),
      shared_of (compose_sm mu12 mu23) =
      compose_meminj (shared_of mu12) (shared_of mu23).
Proof. intros. unfold shared_of. 
  rewrite compose_sm_pub; trivial.
  rewrite compose_sm_foreign; trivial.
  unfold join, compose_meminj. extensionality b.
  remember (foreign_of mu12 b) as f; destruct f; apply eq_sym in Heqf.
    destruct p as [b2 d1].
    destruct (foreign_DomRng _ WD1 _ _ _ Heqf) as [A [B [C [D [E [F [G H]]]]]]].
    apply HypFrg in F.
    destruct (frgnSrc _ WD2 _ F) as [b3 [d2 [FRG2 TGT2]]].
    rewrite FRG2. trivial.
  remember (pub_of mu12 b) as d; destruct d; apply eq_sym in Heqd; trivial.
    destruct p as [b2 d1].
    destruct (pub_locBlocks _ WD1 _ _ _ Heqd) as [A [B [C [D [E [F [G H]]]]]]].
    apply HypPub in B.
    destruct (pubSrc _ WD2 _ B) as [b3 [d2 [PUB2 TGT2]]].
    rewrite PUB2.
    apply (pubBlocksLocalSrc _ WD2) in B.
    apply (locBlocksSrc_frgnBlocksSrc _ WD2) in B.
    unfold foreign_of. destruct mu23. simpl in *. rewrite B. trivial.
Qed.

Lemma compose_sm_wd: forall mu1 mu2 (WD1: SM_wd mu1) (WD2:SM_wd mu2)
         (HypPub: forall b, pubBlocksTgt mu1 b = true ->
                            pubBlocksSrc mu2 b = true)
         (HypFrg: forall b, frgnBlocksTgt mu1 b = true ->
                            frgnBlocksSrc mu2 b = true),
      SM_wd (compose_sm mu1 mu2).
Proof. intros.
  destruct mu1 as [locBSrc1 locBTgt1 pSrc1 pTgt1 local1 extBSrc1 extBTgt1 fSrc1 fTgt1 extern1]; simpl.
  destruct mu2 as [locBSrc2 locBTgt2 pSrc2 pTgt2 local2 extBSrc2 extBTgt2 fSrc2 fTgt2 extern2]; simpl.
split; simpl in *.
apply WD1.
apply WD2.
(*local_DomRng*)
  intros b1 b3 d H. 
  destruct (compose_meminjD_Some _ _ _ _ _ H) 
    as [b2 [d1 [d2 [PUB1 [PUB2 X]]]]]; subst; clear H.
  split. eapply WD1. apply PUB1. 
         eapply WD2. apply PUB2. 
(*extern_DomRng*)
  intros b1 b3 d H. 
  destruct (compose_meminjD_Some _ _ _ _ _ H) 
    as [b2 [d1 [d2 [EXT1 [EXT2 X]]]]]; subst; clear H.
  split. eapply WD1. apply EXT1. 
         eapply WD2. apply EXT2. 
(*pubSrc*)
  intros. 
  destruct (pubSrc _ WD1 _ H) as [b2 [d1 [Loc1 Tgt1]]]. simpl in *.
  apply HypPub in Tgt1. 
  destruct (pubSrc _ WD2 _ Tgt1) as [b3 [d2 [Loc2 Tgt2]]]. simpl in *.
  unfold compose_meminj. exists b3, (d1+d2).
  rewrite H in *. rewrite Tgt1 in *. rewrite Loc1. rewrite Loc2. auto.
(*frgnSrc*)
  intros.
  destruct (frgnSrc _ WD1 _ H) as [b2 [d1 [Ext1 Tgt1]]]. simpl in *.
  apply HypFrg in Tgt1. 
  destruct (frgnSrc _ WD2 _ Tgt1) as [b3 [d2 [Ext2 Tgt2]]]. simpl in *.
  unfold compose_meminj. exists b3, (d1+d2).
  rewrite H in *. rewrite Tgt1 in *. rewrite Ext1. rewrite Ext2. auto.
(*locBlocksDomTgt*)
  apply WD2.
(*frgnBlocksDomTgt*)
  apply WD2.
Qed.

Lemma compose_sm_as_inj: forall mu12 mu23 (WD1: SM_wd mu12) (WD2: SM_wd mu23)
   (SrcTgtLoc: locBlocksTgt mu12 = locBlocksSrc mu23)
   (SrcTgtExt: extBlocksTgt mu12 = extBlocksSrc mu23),
   as_inj (compose_sm mu12 mu23) = 
   compose_meminj (as_inj mu12) (as_inj mu23).
Proof. intros.
  unfold as_inj.
  rewrite compose_sm_extern.
  rewrite compose_sm_local.
  unfold join, compose_meminj. extensionality b.
  remember (extern_of mu12 b) as f; destruct f; apply eq_sym in Heqf.
    destruct p as [b2 d1].
    remember (extern_of mu23 b2) as d; destruct d; apply eq_sym in Heqd.
      destruct p as [b3 d2]. trivial.
    destruct (disjoint_extern_local _ WD1 b).
       rewrite H in Heqf. discriminate.
    rewrite H. 
    destruct (extern_DomRng _ WD1 _ _ _ Heqf) as [A B]. 
    rewrite SrcTgtExt in B.
    remember (local_of mu23 b2) as q; destruct q; trivial; apply eq_sym in Heqq.
    destruct p as [b3 d2].
    destruct (local_DomRng _ WD2 _ _ _ Heqq) as [AA BB].
    destruct (disjoint_extern_local_Src _ WD2 b2); congruence. 
  remember (local_of mu12 b) as q; destruct q; trivial; apply eq_sym in Heqq.
    destruct p as [b2 d1].
    destruct (local_DomRng _ WD1 _ _ _ Heqq) as [AA BB].
    remember (extern_of mu23 b2) as d; destruct d; trivial; apply eq_sym in Heqd.
      destruct p as [b3 d2].
      destruct (extern_DomRng _ WD2 _ _ _ Heqd) as [A B]. 
      rewrite SrcTgtLoc in BB.
      destruct (disjoint_extern_local_Src _ WD2 b2); congruence.  
Qed.

Lemma compose_sm_intern_incr:
      forall mu12 mu12' mu23 mu23'
            (inc12: intern_incr mu12 mu12') 
            (inc23: intern_incr mu23 mu23'),
      intern_incr (compose_sm mu12 mu23) (compose_sm mu12' mu23').
Proof. intros.
split; simpl in *.
    eapply compose_meminj_inject_incr.
        apply inc12.
        apply intern_incr_local; eassumption.
split. rewrite (intern_incr_extern _ _ inc12).
       rewrite (intern_incr_extern _ _ inc23).
       trivial.
split. apply inc12.
split. apply inc23.
split. apply inc12.
split. apply inc23.
split. apply inc12.
split. apply inc23.
split. apply inc12.
apply inc23.
Qed.

Lemma compose_sm_extern_incr:
      forall mu12 mu12' mu23 mu23'
            (inc12: extern_incr mu12 mu12') 
            (inc23: extern_incr mu23 mu23')
  (FRG': forall b1 b2 d1, foreign_of mu12' b1 = Some(b2,d1) ->
         exists b3 d2, foreign_of mu23' b2 = Some(b3,d2))
  (WD12': SM_wd mu12') (WD23': SM_wd mu23'),
  extern_incr (compose_sm mu12 mu23) (compose_sm mu12' mu23').
Proof. intros.
split; intros.
  rewrite compose_sm_extern.
  rewrite compose_sm_extern.
  eapply compose_meminj_inject_incr.
    apply inc12.
    apply extern_incr_extern; eassumption.
split; simpl.
  rewrite (extern_incr_local _ _ inc12). 
  rewrite (extern_incr_local _ _ inc23).
  trivial.
split. apply inc12.
split. apply inc23.
split. apply inc12.
split. apply inc23.
split. apply inc12.
split. apply inc23.
split. apply inc12.
apply inc23.
Qed.

Lemma extern_incr_inject_incr: 
      forall nu12 nu23 nu' (WDnu' : SM_wd nu')
          (EXT: extern_incr (compose_sm nu12 nu23) nu')
          (GlueInvNu: SM_wd nu12 /\ SM_wd nu23 /\
                      locBlocksTgt nu12 = locBlocksSrc nu23 /\
                      extBlocksTgt nu12 = extBlocksSrc nu23 /\
                      (forall b, pubBlocksTgt nu12 b = true -> 
                                 pubBlocksSrc nu23 b = true) /\
                      (forall b, frgnBlocksTgt nu12 b = true -> 
                                 frgnBlocksSrc nu23 b = true)),
      inject_incr (compose_meminj (as_inj nu12) (as_inj nu23)) (as_inj nu').
Proof. intros.
  intros b; intros.
  destruct (compose_meminjD_Some _ _ _ _ _ H)
    as [b2 [d1 [d2 [Nu12 [Nu23 D]]]]]; subst; clear H.
  unfold extern_incr in EXT. simpl in EXT.
  destruct EXT as [EXT [LOC [extBSrc12 [extBTgt23 [locBSrc12 [locBTgt23 [pubBSrc12 [pubBTgt23 [frgnBSrc12 frgnBTgt23]]]]]]]]].
  destruct (joinD_Some _ _ _ _ _ Nu12); clear Nu12.
  (*extern12*)
     destruct (joinD_Some _ _ _ _ _ Nu23); clear Nu23.
     (*extern12*)
        apply join_incr_left. apply EXT.
        unfold compose_meminj. rewrite H. rewrite H0. trivial.
     (*local*)
        destruct H0.
        destruct GlueInvNu as [GLa [GLb [GLc [GLd [GLe GLf]]]]].
        destruct (extern_DomRng' _ GLa _ _ _ H) as [? [? [? [? [? [? [? ?]]]]]]].
        destruct (local_locBlocks _ GLb _ _ _ H1) as [? [? [? [? [? [? [? ?]]]]]]].
        rewrite GLd in *. congruence.  
  (*local*) 
     destruct H.
     destruct (joinD_Some _ _ _ _ _ Nu23); clear Nu23.
     (*extern12*)
        destruct GlueInvNu as [GLa [GLb [GLc [GLd [GLe GLf]]]]].
        destruct (extern_DomRng' _ GLb _ _ _ H1) as [? [? [? [? [? ?]]]]].
        destruct (local_locBlocks _ GLa _ _ _ H0) as [? [? [? [? [? ?]]]]].
        rewrite GLd in *. congruence. 
     (*local*)
        destruct H1. 
        apply join_incr_right. eapply disjoint_extern_local. apply WDnu'.
        rewrite <- LOC. unfold compose_meminj.
        rewrite H0, H2. trivial.
Qed.

Lemma compose_sm_as_injD: forall mu1 mu2 b1 b3 d
      (I: as_inj (compose_sm mu1 mu2) b1 = Some (b3, d))
      (WD1: SM_wd mu1) (WD2: SM_wd mu2),
      exists b2 d1 d2, as_inj mu1 b1 = Some(b2,d1) /\
                       as_inj mu2 b2 = Some(b3,d2) /\
                       d=d1+d2.
Proof. intros.
destruct (joinD_Some _ _ _ _ _ I); clear I.
(*extern*)
  rewrite compose_sm_extern in H.
  destruct (compose_meminjD_Some _ _ _ _ _ H)
      as [b2 [d1 [d2 [EXT1 [EXT2 D]]]]]; clear H.
  exists b2, d1, d2.
  split. apply join_incr_left. assumption.
  split. apply join_incr_left. assumption.
         assumption. 
(*local*)
  destruct H. 
  rewrite compose_sm_extern in H.
  rewrite compose_sm_local in H0.
  destruct (compose_meminjD_Some _ _ _ _ _ H0)
      as [b2 [d1 [d2 [LOC1 [LOC2 D]]]]]; clear H0.
  exists b2, d1, d2.
  split. apply join_incr_right.
           apply disjoint_extern_local; assumption. 
           assumption.
  split. apply join_incr_right.
           apply disjoint_extern_local; assumption. 
           assumption.
         assumption.
Qed.

Lemma compose_sm_as_injD_None:
  forall (mu1 mu2 : SM_Injection) b1,
       SM_wd mu1 ->
       SM_wd mu2 ->
    (locBlocksTgt mu1 = locBlocksSrc mu2 /\
         extBlocksTgt mu1 = extBlocksSrc mu2) ->
       as_inj (compose_sm mu1 mu2) b1 = None ->
         as_inj mu1 b1 = None  \/
         exists b2 d, (as_inj mu1 b1 = Some (b2, d) /\ as_inj mu2 b2 = None).
Proof.
intros mu1 mu2 b1 SMWD1 SMWD2 [GLUEloc GLUEext].
unfold as_inj, join, compose_sm; simpl.
destruct (Values.compose_meminj (extern_of mu1) (extern_of mu2) b1) as [[b2 delta]| ] eqn:extmap.
discriminate.
destruct (Values.compose_meminj (local_of mu1) (local_of mu2) b1) as [[b2 delta]| ] eqn:locmap.
discriminate.
intros tautology.
destruct (compose_meminjD_None _ _ _ extmap) as [extmap' | [b' [ofs' [extmap1 extmap2]]]];
destruct (compose_meminjD_None _ _ _ locmap) as [locmap' | [b'' [ofs'' [locmap1 locmap2]]]].
- rewrite extmap'; simpl.  rewrite locmap'; auto.
- rewrite extmap'; simpl. right.
  exists b'', ofs''. split.  
  + auto.
  + destruct (extern_of mu2 b'') as [[b0 d]| ] eqn:extmap0.
    * apply SMWD2 in extmap0. apply SMWD1 in locmap1.
      destruct locmap1; destruct extmap0.
      rewrite GLUEloc in *.
      destruct SMWD2 as [disj_src _].
      destruct (disj_src b'') as [theFalse | theFalse]; rewrite theFalse in *; discriminate.
    * assumption.
- rewrite extmap1; simpl. right.
  exists b', ofs'. split.
  + reflexivity.
  + rewrite extmap2; simpl.
    destruct (local_of mu2 b') as [[b0 d]| ] eqn:locmap0.
    * apply SMWD2 in locmap0. apply SMWD1 in extmap1.
      destruct extmap1; destruct locmap0.
      rewrite GLUEext in *.
      destruct SMWD2 as [disj_src _].
      destruct (disj_src b') as [theFalse | theFalse]; rewrite theFalse in *; discriminate.
    * assumption.
- apply SMWD1 in extmap1; apply SMWD1 in locmap1.
  destruct locmap1; destruct extmap1.
  destruct SMWD1 as [disj_src _].
  destruct (disj_src b1) as [theFalse | theFalse]; rewrite theFalse in *; discriminate.
Qed.  

(*
Lemma compose_sm_intern_separated:
      forall mu12 mu12' mu23 mu23' m1 m2 m3 
        (inc12: intern_incr mu12 mu12') 
        (inc23: intern_incr mu23 mu23')
        (InjSep12 : sm_inject_separated mu12 mu12' m1 m2)
        (InjSep23 : sm_inject_separated mu23 mu23' m2 m3)
        (WD12: SM_wd mu12) (WD12': SM_wd mu12') (WD23: SM_wd mu23) (WD23': SM_wd mu23')
        (BlocksLoc: locBlocksTgt mu12 = locBlocksSrc mu23)
        (BlocksExt: extBlocksTgt mu12 = extBlocksSrc mu23),
      sm_inject_separated (compose_sm mu12 mu23)
                          (compose_sm mu12' mu23') m1 m3.
Proof. intros.
destruct InjSep12 as [AsInj12 [DomTgt12 Sep12]].
destruct InjSep23 as [AsInj23 [DomTgt23 Sep23]].
split.
  intros b1 b3 d; intros.
  simpl.
  destruct (compose_sm_as_injD _ _ _ _ _ H0)
     as [b2 [d1 [d2 [AI12' [AI23' X]]]]]; subst; trivial; clear H0.
  rewrite compose_sm_DomSrc, compose_sm_DomTgt.
  assert (DomSrc (compose_sm mu12' mu23') b1 = true /\
          DomTgt (compose_sm mu12' mu23') b3 = true).
    rewrite compose_sm_DomSrc, compose_sm_DomTgt.
    split. eapply as_inj_DomRng; eassumption.
           eapply as_inj_DomRng; eassumption. 
  destruct H0 as [DOM1 TGT3]; simpl in *.
  assert (TGT2: DomTgt mu12' b2 = true).
    eapply as_inj_DomRng. eassumption. eapply WD12'.
  assert (DOMB2: DomSrc mu23' b2 = true).
    eapply as_inj_DomRng. eassumption. eapply WD23'.
  rewrite compose_sm_DomSrc, compose_sm_DomTgt in *.
  remember (as_inj mu12 b1) as q.
  destruct q; apply eq_sym in Heqq.
    destruct p.
    specialize (intern_incr_as_inj _ _ inc12 WD12' _ _ _ Heqq); intros.
    rewrite AI12' in H0. apply eq_sym in H0. inv H0.
    destruct (joinD_Some _ _ _ _ _ Heqq); clear Heqq.
    (*extern12Some*)
       assert (extern_of mu12' b1 = Some (b2, d1)).
          rewrite <- (intern_incr_extern _ _ inc12). assumption.
       destruct (joinD_None _ _ _ H); clear H.
       clear AI12'.
       destruct (joinD_Some _ _ _ _ _ AI23'); clear AI23'.
       (*extern23'Some*)
         assert (extern_of mu23 b2 = Some (b3, d2)).
           rewrite (intern_incr_extern _ _ inc23). assumption.
         rewrite compose_sm_extern in H2.
         unfold compose_meminj in H2. 
         rewrite H0 in H2. rewrite H4 in H2. inv H2.
       (*extern23'None*)
         destruct H.
         rewrite compose_sm_extern in H2.
         destruct (compose_meminjD_None _ _ _ H2); clear H2.
            rewrite H5 in H0. discriminate.
         destruct H5 as [bb2 [dd1 [EXT12 EXT23]]].
         rewrite EXT12 in H0. inv H0.
         rewrite compose_sm_local in H3.
         remember (local_of mu23 b2) as qq.
         destruct qq; apply eq_sym in Heqqq.
            destruct p.
            specialize (intern_incr_local _ _ inc23); intros.
            specialize (H0 _ _ _ Heqqq). rewrite H0 in H4. inv H4.
            destruct (extern_DomRng _ WD12 _ _ _ EXT12) as [A B].
            destruct (local_DomRng _ WD23 _ _ _ Heqqq) as [AA BB].
            rewrite BlocksExt in B. 
            destruct (disjoint_extern_local_Src _ WD23 b2); congruence.
         destruct (AsInj23 b2 b3 d2).
            apply joinI_None. assumption. assumption.
            apply join_incr_right.
              apply disjoint_extern_local. assumption.
              assumption.
         destruct (extern_DomRng _ WD12 _ _ _ EXT12) as [XX YY].
           rewrite BlocksExt in YY. unfold DomSrc in H0.
           rewrite YY in H0. rewrite orb_comm in H0. discriminate.
    (*extern12None*)
       destruct H0.
       assert (extern_of mu12' b1 = None).
          rewrite <- (intern_incr_extern _ _ inc12). assumption.
       assert (local_of mu12' b1 = Some (b2, d1)).
          eapply (intern_incr_local _ _ inc12). assumption.
       destruct (joinD_None _ _ _ H); clear H.
       clear AI12'.
       destruct (joinD_Some _ _ _ _ _ AI23'); clear AI23'.
       (*extern23'Some*)
         destruct (local_DomRng _ WD12' _ _ _ H3) as [AA BB].
         destruct (extern_DomRng _ WD23' _ _ _ H) as [A B].
         destruct (local_DomRng _ WD12 _ _ _ H1) as [AAA BBB].
         rewrite BlocksLoc in BBB. 
         assert (locBlocksSrc mu23' b2 = true). apply inc23. assumption.
         destruct (disjoint_extern_local_Src _ WD23' b2); congruence.
       (*extern23'None*)
         destruct H.
         assert (extern_of mu23 b2 = None).
           rewrite (intern_incr_extern _ _ inc23). assumption.
         rewrite compose_sm_local in H5.
         unfold compose_meminj in H5. rewrite H1 in H5.
         remember (local_of mu23 b2).
         destruct o. destruct p. inv H5. clear H5. apply eq_sym in Heqo.
         clear H4.
         destruct (local_DomRng _ WD12 _ _ _ H1) as [AA BB].
         assert (DomSrc mu23 b2 = false /\ DomTgt mu23 b3 = false).
            eapply AsInj23.
              apply joinI_None; assumption.
              apply join_incr_right; try eassumption.
                apply disjoint_extern_local; eassumption.
         destruct H4.  
         destruct (local_locBlocks _ WD12 _ _ _ H1) 
           as [AAA [BBB [CCC [DDD [EEE FFF]]]]].
         rewrite BlocksLoc in BBB. unfold DomSrc in H4.
             rewrite BBB in H4. discriminate.
   (*as_inj mu12 b1 = None*)
     destruct (AsInj12 _ _ _ Heqq AI12'). split; trivial. clear H.
     remember (as_inj mu23 b2) as d.
     destruct d; apply eq_sym in Heqd.
       destruct p.
       specialize (intern_incr_as_inj _ _ inc23 WD23' _ _ _ Heqd).
       intros ZZ; rewrite AI23' in ZZ. apply eq_sym in ZZ; inv ZZ.
       destruct (as_inj_DomRng _ _ _ _ Heqd WD23).
       unfold DomSrc in H. unfold DomTgt in H1.
       rewrite BlocksLoc, BlocksExt in H1. rewrite H1 in H; discriminate.
     eapply AsInj23. eassumption. eassumption.
simpl.
  split. apply DomTgt12. apply Sep23.
Qed.*)

Lemma vis_compose_sm: forall mu nu, vis (compose_sm mu nu) = vis mu.
Proof. intros. unfold vis. destruct mu; simpl. reflexivity. Qed.

Lemma restrict_compose: forall j k X, 
  restrict (compose_meminj j k) X = compose_meminj (restrict j X) k.
Proof. intros.
  extensionality b.
  unfold compose_meminj, restrict.
  remember (X b) as d.
  destruct d; trivial.
Qed.
*)

Inductive sem_compose_ord_eq_eq {D12 D23:Type} 
  (ord12: D12 -> D12 -> Prop) (ord23: D23 -> D23 -> Prop) (C2:Type):
  (D12 * option C2 * D23) ->  (D12 * option C2 * D23) ->  Prop := 
| sem_compose_ord1 :
  forall (d12 d12':D12) (c2:C2) (d23:D23),
    ord12 d12 d12' -> sem_compose_ord_eq_eq ord12 ord23 C2 (d12,Some c2,d23) (d12',Some c2,d23)
| sem_compose_ord2 :
  forall (d12 d12':D12) (c2 c2':C2) (d23 d23':D23),
    ord23 d23 d23' -> sem_compose_ord_eq_eq ord12 ord23 C2 (d12,Some c2,d23) (d12',Some c2',d23').

Lemma well_founded_sem_compose_ord_eq_eq: forall {D12 D23:Type}
  (ord12: D12 -> D12 -> Prop) (ord23: D23 -> D23 -> Prop)  (C2:Type)
  (WF12: well_founded ord12) (WF23: well_founded ord23),
  well_founded (sem_compose_ord_eq_eq ord12 ord23 C2). 
Proof. 
  intros. intro. destruct a as [[d12 c2] d23].
  revert d12. 
  destruct c2. 
  2: constructor; intros. 2: inv H.
  revert c. 
  induction d23 using (well_founded_induction WF23).
  intros.
  induction d12 using (well_founded_induction WF12).
  constructor; intros. inv H1.
  generalize (H0 d0). simpl. intros.
  apply H1. auto.
  generalize (H d1). 
  intros. 
  specialize (H1 H4). auto. 
Qed.


Lemma forall_val_inject_split: forall j1 j2 vals1 vals3 
  (V: Forall2 (val_inject (compose_meminj j1 j2)) vals1 vals3),
  exists vals2, Forall2 (val_inject j1) vals1 vals2
             /\ Forall2 (val_inject j2) vals2 vals3.
Proof. intros.
  induction V; simpl.
    exists nil; simpl. split; econstructor.
  destruct IHV as [vals [Vals1 Vals2]].
    destruct (val_inject_split _ _ _ _ H) as [z [VV1 VV2]].
    exists (z::vals).
    split; econstructor; eauto.
Qed.

Lemma freshblock_irrefl' m : freshblock m m = fun b => false.
Proof. extensionality b. apply freshblock_irrefl. Qed.

Lemma orb_false_r_ext L: (fun b : block => L b || false) = L.
Proof. extensionality b. rewrite orb_false_r; trivial. Qed.

Lemma fresh_no_alloc m L: (fun b : block => L b || freshblock m m b) = L.
Proof. extensionality b. rewrite freshblock_irrefl, orb_false_r; trivial. Qed.

Lemma freshblock_store m ch b z v m' (ST: Mem.store ch m b z v = Some m'):
      freshblock m m' = fun b => false.
Proof. unfold freshblock. extensionality bb.
  destruct (mem_lemmas.valid_block_dec m' bb); simpl; trivial.
  apply (Mem.store_valid_block_2 _ _ _ _ _ _ ST) in v0.
  destruct (mem_lemmas.valid_block_dec m bb); simpl; trivial; congruence.
Qed.

Lemma freshblock_storev m ch addr v m' (ST: Mem.storev ch m addr v = Some m'):
      freshblock m m' = fun b => false.
Proof. destruct addr; inv ST. eapply freshblock_store; eassumption. Qed.

Lemma freshblock_free m b lo hi m' (FR: Mem.free m b lo hi = Some m'):
      freshblock m m' = fun b => false.
Proof. unfold freshblock. extensionality bb.
  destruct (mem_lemmas.valid_block_dec m' bb); simpl; trivial.
  apply (Mem.valid_block_free_2 _ _ _ _ _ FR) in v.
  destruct (mem_lemmas.valid_block_dec m bb); simpl; trivial; congruence.
Qed. 
Lemma freshblock_free' m b lo hi m' (FR: Mem.free m b lo hi = Some m') bb:
      freshblock m m' bb = false.
Proof. rewrite (freshblock_free _ _ _ _ _ FR); trivial. Qed.  

Lemma freshblock_free_list': forall l m m' (FR: Mem.free_list m l = Some m') b,
      freshblock m m' b = false.
Proof. induction l; simpl; intros; inv FR.
 apply freshblock_irrefl.
 destruct a as [[bb lo] hi]. remember (Mem.free m bb lo hi) as d.
   symmetry in Heqd; destruct d; inv H0. 
   apply freshblock_charF.
   apply freshblock_free' with (bb:=b) in Heqd.
   specialize (IHl _ _ H1 b). 
   apply freshblock_charF in IHl. 
   apply freshblock_charF in Heqd. intuition.
Qed. 
Lemma freshblock_free_list l m m' (FR: Mem.free_list m l = Some m'):
      freshblock m m' = fun b => false.
Proof. extensionality bb. eapply freshblock_free_list'; eassumption. Qed.

Lemma freshblock_alloc m b lo hi m' (FR: Mem.alloc m lo hi = (m',b)):
      freshblock m m' = eq_block b.
Proof. unfold freshblock. extensionality bb.
  destruct (mem_lemmas.valid_block_dec m' bb); simpl; trivial.
  + destruct (Mem.valid_block_alloc_inv _ _ _ _ _ FR _ v); subst.
       apply Mem.fresh_block_alloc in FR.
       destruct (mem_lemmas.valid_block_dec m b). contradiction. simpl.
       destruct (eq_block b b); simpl; trivial. congruence.
    destruct (mem_lemmas.valid_block_dec m bb); simpl; try contradiction.
      apply Mem.fresh_block_alloc in FR.
      destruct (eq_block b bb); subst; try contradiction. reflexivity.
  + apply Mem.valid_new_block in FR. destruct (eq_block b bb); subst; try contradiction. reflexivity.
Qed.

Lemma extends_extends_freshblock m1 m2 m1' m2'
   (EXT: Mem.extends m1 m2) (EXT': Mem.extends m1' m2'):
   freshblock m2 m2' = freshblock m1 m1'.
Proof. extensionality b.
    unfold freshblock. 
           destruct (valid_block_dec m1 b); simpl.
           + destruct (valid_block_dec m2 b); simpl.
             - do 2 rewrite andb_false_r; trivial.
             - elim n. eapply (Mem.valid_block_extends _ _ _ EXT); trivial.
           + destruct (valid_block_dec m2 b); simpl.
             - elim n. eapply (Mem.valid_block_extends _ _ _ EXT); trivial.
             - do 2 rewrite andb_true_r.
               destruct (valid_block_dec m1' b); destruct (valid_block_dec m2' b); trivial.
               * elim n1; eapply (Mem.valid_block_extends _ _ _ EXT'); trivial.
               * elim n1; eapply (Mem.valid_block_extends _ _ _ EXT'); trivial.
Qed.

Lemma mini_intern_incr_same_meminj j L1 L2: mini_intern_incr j j L1 L2.
Proof. split. apply inject_incr_refl. congruence. Qed.

Lemma globals_separate_same_meminj {F2 V2} m1(g2:Genv.t F2 V2) j: 
      globals_separate m1 g2 j j.
Proof. red; congruence. Qed.
(*
Lemma mini_locally_allocated_same L1 L2 m m2:
      mini_locally_allocated L1 L2 m m2 L1 L2 m m2.
Proof. red. do 2 rewrite fresh_no_alloc; split; trivial. Qed.

Lemma mini_locally_allocated_storev chunk m a v m' tm ta tv tm' L1 L2
  (ST: Mem.storev chunk m a v = Some m')
  (TST: Mem.storev chunk tm ta tv = Some tm'):
mini_locally_allocated L1 L2 m tm L1 L2 m' tm'.
Proof.
  red; intros. erewrite freshblock_storev; try eassumption. 
  erewrite freshblock_storev; try eassumption. 
  do 2 rewrite orb_false_r_ext. split; trivial.
Qed.

Lemma mini_locally_allocated_parallel_free m b lo hi m' tm tb tlo thi tm' L1 L2
  (FR: Mem.free m b lo hi = Some m')
  (TFR: Mem.free tm tb tlo thi = Some tm'):
mini_locally_allocated L1 L2 m tm L1 L2 m' tm'.
Proof.
   red. erewrite freshblock_free; try eassumption.
  erewrite freshblock_free; try eassumption. 
  do 2 rewrite orb_false_r_ext. split; trivial.
Qed.
*)
(*Adapted from sepcomp.effect_properties's ...PropagateLeft*)
Lemma StoreEffect_propagate_inj m b i0 v chunk m'
      (ST1 : Mem.store chunk m b (Int.unsigned i0) v = Some m') j m2
      (MINJ : Mem.inject j m m2) bb ofs 
      delta (J: j b = Some (bb, delta)) v'
      (Hoff : Int.unsigned (Int.add i0 (Int.repr delta)) <= ofs <
         Int.unsigned (Int.add i0 (Int.repr delta)) +
         Z.of_nat (length (encode_val chunk v'))):
exists (b1 : block) (delta0 : Z),
  j b1 = Some (bb, delta0) /\
  StoreEffect (Vptr b i0) (encode_val chunk v) b1 (ofs - delta0) = true.
Proof. exists b, delta. split; trivial.
      unfold StoreEffect. destruct (eq_block b b); simpl; try congruence.
      clear e. rewrite encode_val_length, <- size_chunk_conv in *.
      assert (Arith: Int.unsigned i0 <= ofs - delta < Int.unsigned i0 + size_chunk chunk).
         assert (DD: delta >= 0 /\ 0 <= Int.unsigned i0 + delta <= Int.max_unsigned).
                 eapply MINJ. eassumption. left. eapply Mem.perm_implies. eapply Mem.perm_max.
                 eapply Mem.store_valid_access_3. eassumption. omega. constructor.
         destruct DD as [DD1 DD2].
         specialize (Int.unsigned_range i0); intros I.
         assert (URdelta: Int.unsigned (Int.repr delta) = delta).
            apply Int.unsigned_repr. split; omega. 

         rewrite Int.add_unsigned in Hoff. rewrite URdelta in Hoff.
         rewrite (Int.unsigned_repr _ DD2) in Hoff. omega. clear Hoff. 
      destruct (zle (Int.unsigned i0) (ofs - delta)); simpl; try omega.
      destruct (zlt (ofs - delta) (Int.unsigned i0 + size_chunk chunk)); simpl; trivial.
      omega.  
Qed.

Lemma StoreEffect_propagate_ext chunk m a v m'
      (ST: Mem.storev chunk m a v = Some m')
      L a' (ALD : Val.lessdef a a') v' b ofs 
      (EFF: effect_semantics.StoreEffect a' (encode_val chunk v') b ofs = true):
  L b = true \/
  effect_semantics.StoreEffect a (encode_val chunk v) b ofs = true.
Proof.
  apply effect_semantics.StoreEffectD in EFF. destruct EFF as [i [A Arith]].
  subst a'. destruct a; simpl in ST; try discriminate. simpl.
  inv ALD. right. destruct (eq_block b b). 2: elim n; trivial. simpl; clear e.
  destruct (zle (Int.unsigned i) ofs); simpl in *; try omega.
  rewrite encode_val_length, <- size_chunk_conv in *.
  destruct (zlt ofs (Int.unsigned i + size_chunk chunk)); trivial; omega.
Qed.


Lemma effstep_one_star_one_star_one_plus:
  forall (G C : Type) (Sem : EffectSem G C)
    (ge : G) U1 c1 m1 U2 c2 m2 U3 c3 m3 U4 c4 m4 U5 c5 m5 U6 c6 m6,
  effstep Sem ge U1 c1 m1 c2 m2 ->
  effstep_star Sem ge U2 c2 m2 c3 m3 ->
  effstep Sem ge U3 c3 m3 c4 m4 ->
  effstep_star Sem ge U4 c4 m4 c5 m5 ->
  effstep Sem ge U5 c5 m5 c6 m6 ->
  U6 = (fun b z => U1 b z || (U2 b z || (U3 b z || (U4 b z || U5 b z && valid_block_dec m4 b) && valid_block_dec m3 b) &&
        valid_block_dec m2 b) && valid_block_dec m1 b) ->
  effstep_plus Sem ge U6 c1 m1 c6 m6.
Proof. intros.
  eapply effstep_plus_star_trans'.
    eapply effstep_plus_one; eauto. clear H.
    eapply effstep_star_trans'; eauto. clear H0.
  eapply effstep_star_trans'.
    eapply effstep_star_one; eauto. clear H1.
    eapply effstep_star_trans'; eauto. clear H2.
    eapply effstep_star_one; eauto. reflexivity. reflexivity. reflexivity. trivial. 
Qed.

Lemma effstep_one_star_star_plus:
  forall (G C : Type) (Sem : EffectSem G C)
    (ge : G) U1 c1 m1 U2 c2 m2 U3 c3 m3 U4 c4 m4,
  effstep Sem ge U1 c1 m1 c2 m2 ->
  effstep_star Sem ge U2 c2 m2 c3 m3 ->
  effstep_star Sem ge U3 c3 m3 c4 m4 ->
  U4 = (fun b z => U1 b z || (U2 b z || U3 b z && valid_block_dec m2 b) && valid_block_dec m1 b) ->
  effstep_plus Sem ge U4 c1 m1 c4 m4.
Proof. intros.
  eapply effstep_plus_star_trans'.
    eapply effstep_plus_one; eauto. 
    eapply effstep_star_trans; eauto. trivial.
Qed.

Lemma effstep_one_star_one_plus:
  forall (G C : Type) (Sem : EffectSem G C)
    (ge : G) U1 c1 m1 U2 c2 m2 U3 c3 m3 U4 c4 m4,
  effstep Sem ge U1 c1 m1 c2 m2 ->
  effstep_star Sem ge U2 c2 m2 c3 m3 ->
  effstep Sem ge U3 c3 m3 c4 m4 ->
  U4 = (fun b z => U1 b z || (U2 b z || U3 b z && valid_block_dec m2 b) && valid_block_dec m1 b) ->
  effstep_plus Sem ge U4 c1 m1 c4 m4.
Proof. intros.
  eapply effstep_one_star_star_plus; eauto.
    eapply effstep_star_one; eauto. 
Qed.

Lemma effstep_one_star_plus:
  forall (G C : Type) (Sem : EffectSem G C)
    (ge : G) U1 c1 m1 U2 c2 m2 U3 c3 m3,
  effstep Sem ge U1 c1 m1 c2 m2 ->
  effstep_star Sem ge U2 c2 m2 c3 m3 ->
  U3 = (fun (b : block) (z : Z) => U1 b z || U2 b z && valid_block_dec m1 b) ->
  effstep_plus Sem ge U3 c1 m1 c3 m3.
Proof. intros.
  eapply effstep_plus_star_trans'; eauto.  
    eapply effstep_plus_one; eauto. 
Qed.

Lemma effstep_one_plus_plus:
  forall (G C : Type) (Sem : EffectSem G C)
    (ge : G) U1 c1 m1 U2 c2 m2 U3 c3 m3,
  effstep Sem ge U1 c1 m1 c2 m2 ->
  effstep_plus Sem ge U2 c2 m2 c3 m3 ->
  U3 = (fun (b : block) (z : Z) => U1 b z || U2 b z && valid_block_dec m1 b) ->
  effstep_plus Sem ge U3 c1 m1 c3 m3.
Proof. intros.
  eapply effstep_plus_trans'; eauto.  
    eapply effstep_plus_one; eauto. 
Qed.

Lemma effstep_star_plus:
  forall (G C : Type) (Sem : EffectSem G C)
    (ge : G) U c1 m1 c2 m2,
  effstep_plus Sem ge U c1 m1 c2 m2 ->
  effstep_star Sem ge U c1 m1 c2 m2.
Proof. intros. destruct H. eexists; eassumption. Qed.

