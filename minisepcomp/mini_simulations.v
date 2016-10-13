Require Import Coq.Bool.Bool.

Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import compcert.lib.Coqlib.
Require Import compcert.common.Events.
Require Import compcert.lib.Maps.
Require Import compcert.lib.Integers.
Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.
Require Import compcert.lib.Axioms.

Require Import sepcomp.mem_lemmas.
Require Import sepcomp.semantics.
Require Import sepcomp.effect_semantics.
Require Import msl.Axioms.

Require Import sepcomp.semantics_lemmas.

Require Import minisepcomp.BuiltinEffects.

(** * Structured Simulations *) 

Definition freshblock (m m' : mem) (b : block):=
  valid_block_dec m' b && negb (valid_block_dec m b).

Definition freshblockProp (m m' : mem) (b : block):=
  Mem.valid_block m' b /\ ~ Mem.valid_block m b.

Definition asProp (L: block -> bool): block -> Prop := fun b => L b = true.

Lemma freshblock_asProp m m': freshblockProp m m' = asProp (freshblock m m').
Proof. unfold freshblock, freshblockProp, asProp.
extensionality b. apply prop_ext.
destruct (valid_block_dec m b); destruct (valid_block_dec m' b); intuition.
Qed.

Definition mini_locally_allocated L1 L2 m1 m2 L1' L2' m1' m2' :=
   L1' = (fun b : block => L1 b || freshblock m1 m1' b) /\
   L2' = (fun b : block => L2 b || freshblock m2 m2' b).

Definition mini_intern_incr (j j':meminj) L1' L2':= 
 inject_incr j j' /\
 (forall b1 b2 d (J: j b1 = None) (J': j' b1 = Some(b2, d)),
  L1' b1 = true /\ L2' b2 = true).

Definition mini_extern_incr (j j':meminj) L1 L2:= 
 inject_incr j j' /\
 (forall b1 b2 d (J: j b1 = None) (J': j' b1 = Some(b2, d)),
  L1 b1 = false /\ L2 b2 = false).

Definition globals_separate {F2 V2:Type} (m1:mem) (ge2: Genv.t F2 V2) (j j':meminj) :=
    forall b1 b2 d (J:j b1 = None) (J': j' b1 =Some(b2,d)),
            (*isGlobalBlock ge b2 = false*)
    ~ Mem.valid_block m1 b1 /\ Ple (Genv.genv_next ge2) b2.

Definition meminj_valid (j:meminj) L1 m1 L2 m2 :=
    (forall b, L1 b = true -> Mem.valid_block m1 b) /\
    (forall b, L2 b = true -> Mem.valid_block m2 b) /\
    (forall b1 b2 delta (J: j b1 =Some(b2,delta)), Mem.valid_block m1 b1 /\ Mem.valid_block m2 b2).


(*TODO: adpt this definition to sets B1 B2, (add L1/L2?) and allow readonly blocks to be mapped to "arbitrary" b', d
Definition RDOnly_inj (m1 m2:mem) (j:meminj) B1 :=
  forall b (Hb: B1 b = true),
            j b = Some(b,0) /\ (forall b' d, j b' = Some(b,d) -> b'=b) /\ 
            forall ofs, ~ Mem.perm m1 b ofs Max Writable /\
                        ~ Mem.perm m2 b ofs Max Writable.
*) 

Module Mini_simulation_inj. Section Mini_simulation_injects. 

(** Simulations are parameterized by a source interaction semantics
    [Sem1] and by a target interaction semantics [Sem2]. *)

(** [ge1] and [ge2] are the global environments associated with [Sem1] and
    [Sem2] respectively. *)

Context 
  {F1 V1 C1 F2 V2 C2 : Type}
  (Sem1 : @EffectSem (Genv.t F1 V1) C1)
  (Sem2 : @EffectSem (Genv.t F2 V2) C2)
  (ge1 : Genv.t F1 V1)
  (ge2 : Genv.t F2 V2).

Record Mini_simulation_inject := { 
  (** The type of auxiliary data used to model stuttering. *)
  core_data : Type

  (** The (existentially quantified) match-state relation of the simulation. *)
; match_state : core_data -> meminj -> (block -> bool) -> C1 -> mem -> (block -> bool) -> C2 -> mem -> Prop

  (** A well-founded order on values of type [core_data]. *)
; core_ord : core_data -> core_data -> Prop
; core_ord_wf : well_founded core_ord

  (** The match relation implies that [mu] is well-defined. *)
; match_wd:  
    forall d j L1 c1 m1 L2 c2 m2 (MS: match_state d j L1 c1 m1 L2 c2 m2)
    b1 b2 d (J:j b1=Some(b2, d)), L1 b1 = L2 b2 
(*
  (** The global environments have equal domain. *)
; genvs_dom_eq : genvs_domain_eq ge1 ge2
*)
  (** The static environments are equivalent*)
; senvs_dom_eq : Senv.equiv ge1 ge2

(*  (** The global environments also associate same info with global blocks and 
      preserve find_var. These conditions are used for in the transitivity proof,
      to establish mem_respects_readonly for the intermediate memory and globalenv. *)
; ginfo_preserved : (*gvar_infos_eq ge1 ge2 /\ findsymbols_preserved ge1 ge2 -- subsumed by findsymbols_inject in match_genv?*)*)

  (** The injection [mu] preserves global blocks. *) (*
; match_genv : 
    forall d mu c1 m1 c2 m2 (MC : match_state d mu c1 m1 c2 m2),
    meminj_preserves_globals ge1 (extern_of mu) /\
    (forall b, isGlobalBlock ge1 b = true -> frgnBlocksSrc mu b = true)*)
; match_genv : 
    forall d j L1 c1 m1 L2 c2 m2 (MC : match_state d j L1 c1 m1 L2 c2 m2),
    symbols_inject j ge1 ge2 /\
    meminj_preserves_globals ge1 j /\
    (forall b, isGlobalBlock ge1 b = true -> j b <>None)


  (** The blocks in the domain/range of [mu] are valid in [m1]/[m2]. *)
; match_validblocks : 
    forall d j L1 c1 m1 L2 c2 m2 (MS: match_state d j L1 c1 m1 L2 c2 m2),
    meminj_valid j L1 m1 L2 m2

  (** The clause that relates initial states. *)
; core_initial : 
    forall v vals1 c1 m1 j vals2 m2 (*DomS DomT*),
    initial_core Sem1 ge1 v vals1 = Some c1 ->
    Mem.inject j m1 m2 -> 
    Forall2 (val_inject j) vals1 vals2 ->
    meminj_preserves_globals ge1 j -> symbols_inject j ge1 ge2 ->
    (*globalfunction_ptr_inject ge1 j -> MINI:MAYBE DON'T REMOVE THIS??*)

    mem_respects_readonly ge1 m1 -> mem_respects_readonly ge2 m2 ->

    exists cd, exists c2, 
    initial_core Sem2 ge2 v vals2 = Some c2 
    /\ match_state cd j (fun b => false) c1 m1 (fun b => false) c2 m2

  (** The diagram for internal steps. *)
; effcore_diagram : 
    forall st1 m1 st1' m1' U1, 
    effstep Sem1 ge1 U1 st1 m1 st1' m1' ->
    forall cd st2 j m2 L1 L2,
    match_state cd j L1 st1 m1 L2 st2 m2 ->
    exists st2', exists m2', exists cd', exists j', exists L1', exists L2',
      mini_intern_incr j j' L1' L2'
      /\ globals_separate m1 ge2 j j' 
      /\ mini_locally_allocated L1 L2 m1 m2 L1' L2' m1' m2' 
      /\ match_state cd' j' L1' st1' m1' L2' st2' m2'
      /\ exists U2,              
          ((effstep_plus Sem2 ge2 U2 st2 m2 st2' m2' \/
            (effstep_star Sem2 ge2 U2 st2 m2 st2' m2' /\
             core_ord cd' cd)) /\
          ( forall 
            (UHyp: forall b1 z, U1 b1 z = true -> (L1 b1 = true \/ j b1 <> None))
            b2 ofs (Ub: U2 b2 ofs = true),
            L2 b2 = true \/ (exists b1 delta, j b1 = Some(b2, delta) /\ U1 b1 (ofs-delta) = true))) 

  (** The clause that relates halted states. *)      
; core_halted : 
    forall cd j L1 c1 m1 L2 c2 m2 v1,
    match_state cd j L1 c1 m1 L2 c2 m2 ->
    halted Sem1 c1 = Some v1 ->
    exists v2, 
    Mem.inject j m1 m2 
    /\ mem_respects_readonly ge1 m1 /\ mem_respects_readonly ge2 m2
    /\ val_inject j v1 v2 
    /\ halted Sem2 c2 = Some v2 

  (** The clause that relates [at_external] call points. *)      
; core_at_external : 
    forall cd j L1 c1 m1 L2 c2 m2 e vals1 efsig,
    match_state cd j L1 c1 m1 L2 c2 m2 ->
    at_external Sem1 c1 = Some (e,efsig,vals1) ->
    Mem.inject j m1 m2 
    /\ mem_respects_readonly ge1 m1 /\ mem_respects_readonly ge2 m2
    /\ exists vals2, 
       Forall2 (val_inject j) vals1 vals2 
       /\ at_external Sem2 c2 = Some (e,efsig,vals2)

  (** The diagram for external steps. *)
; eff_after_external: 
    forall cd j L1 st1 L2 st2 m1 e vals1 m2 efsig vals2 e' efsig'
      (MemInjMu: Mem.inject j m1 m2)
      (MatchMu: match_state cd j L1 st1 m1 L2 st2 m2)
      (AtExtSrc: at_external Sem1 st1 = Some (e,efsig,vals1))

        (** We include the clause [AtExtTgt] to ensure that [vals2] is uniquely
         determined. We have [e=e'] and [ef_sig=ef_sig'] by the [at_external]
         clause, but omitting the hypothesis [AtExtTgt] would result in two not
         necesssarily equal target argument lists in language three in the
         transitivity proof, as [val_inject] is not functional in the case in
         which the left value is [Vundef] ([Vundef]s can be refined under memory
         injections to arbitrary values). *)

      (AtExtTgt: at_external Sem2 st2 = Some (e',efsig',vals2)) 
      (ValInjMu: Forall2 (val_inject j) vals1 vals2),

      forall j' ret1 m1' ret2 m2'
        (HasTy1: Val.has_type ret1 (proj_sig_res efsig))
        (HasTy2: Val.has_type ret2 (proj_sig_res efsig'))
        (INC: mini_extern_incr j j' L1 L2) 
        (GSep: globals_separate m1 ge2 j j')

        (MV: meminj_valid j' L1 m1' L2 m2')

        (MemInjNu': Mem.inject j' m1' m2')
        (RValInjNu': val_inject j' ret1 ret2)

        (FwdSrc: mem_forward m1 m1') (FwdTgt: mem_forward m2 m2')
        (RDO1: RDOnly_fwd m1 m1' (ReadOnlyBlocks ge1))
        (RDO2: RDOnly_fwd m2 m2' (ReadOnlyBlocks ge2))

        (UnchSrc: Mem.unchanged_on (fun b1 ofs => L1 b1 = true /\ j b1 = None) m1 m1')
        (UnchTgt: Mem.unchanged_on (o_o_reach j L2 m1) m2 m2') ,

        exists cd', exists st1', exists st2',
          after_external Sem1 (Some ret1) st1 = Some st1' /\
          after_external Sem2 (Some ret2) st2 = Some st2' /\
          match_state cd' j' L1 st1' m1' L2 st2' m2' }.


(** Derive an effectless internal step diagram clause from the effectful diagram
  above. *)

Lemma core_diagram (SMI: Mini_simulation_inject ):
      forall st1 m1 st1' m1', 
        corestep Sem1 ge1 st1 m1 st1' m1' ->
      forall cd L1 L2 st2 j m2,
        match_state SMI cd j L1 st1 m1 L2 st2 m2 ->
        exists st2', exists m2', exists cd', exists j', exists L1', exists L2',
          mini_intern_incr j j' L1' L2' /\
          globals_separate m1 ge2 j j' /\ 
          mini_locally_allocated L1 L2 m1 m2 L1' L2' m1' m2' /\ 
          match_state SMI cd' j' L1' st1' m1' L2' st2' m2' /\
          ((corestep_plus Sem2 ge2 st2 m2 st2' m2') \/
            corestep_star Sem2 ge2 st2 m2 st2' m2' /\
            core_ord SMI cd' cd).
Proof. intros. 
apply effax2 in H. destruct H as [U1 H]. 
exploit (effcore_diagram SMI); eauto.
intros [st2' [m2' [cd' [j' [L1' [L2' [INC [GSEP [LOCALLOC 
  [MST [U2 [STEP _]]]]]]]]]]]].
exists st2', m2', cd', j', L1', L2'.
split; try assumption.
split; try assumption.
split; try assumption.
split; try assumption.
destruct STEP as [[n STEP] | [[n STEP] CO]];
  apply effstepN_corestepN in STEP.
left. exists n. assumption.
right; split; trivial. exists n. assumption.
Qed.

(** Derive an internal step diagram with RDO_fwd property. *)
Lemma effcore_diagram_RDO_fwd (SMI: Mini_simulation_inject): 
      forall st1 m1 st1' m1' U1, 
        effstep Sem1 ge1 U1 st1 m1 st1' m1' ->
      forall cd L1 L2 st2 j m2,
        match_state SMI cd j L1 st1 m1 L2 st2 m2 ->
        exists st2', exists m2', exists cd', exists j', exists L1', exists L2',
          mini_intern_incr j j' L1' L2' /\
          globals_separate m1 ge2 j j' /\ 
          mini_locally_allocated L1 L2 m1 m2 L1' L2' m1' m2' /\ 
          match_state SMI cd' j' L1' st1' m1' L2' st2' m2' /\
        exists U2,
          ((effstep_plus Sem2 ge2 U2 st2 m2 st2' m2' \/
            (effstep_star Sem2 ge2 U2 st2 m2 st2' m2' /\
             core_ord SMI cd' cd)) /\
          ( forall 
            (UHyp: forall b1 z, U1 b1 z = true -> (L1 b1 = true \/ j b1 <> None))
            b2 ofs (Ub: U2 b2 ofs = true),
            L2 b2 = true \/ (exists b1 delta, j b1 = Some(b2, delta) /\ U1 b1 (ofs-delta) = true))
         /\ (forall b, Mem.valid_block m1 b -> readonly m1 b m1')
         /\ (forall b, Mem.valid_block m2 b -> readonly m2 b m2')).
Proof. intros.
  exploit effcore_diagram; eauto. 
  intros [st2' [m2' [cd' [j' [L1' [L2' [INC [LOCALLOC [GSEP [MTCH' [U2 [Steps2 VIS]]]]]]]]]]]].
  exists st2', m2', cd', j', L1', L2'.
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
  exists U2.
  split; trivial.
  split; trivial.
  destruct (match_genv SMI _ _ _ _ _ _ _ _ MTCH').
  split; intros. eapply corestep_rdonly; trivial. eapply effstep_corestep; eassumption.
  destruct Steps2 as [Steps2 | [Steps2 _]].
    apply effstep_plus_corestep_plus in Steps2.
    eapply corestep_plus_rdonly; eassumption.
  apply effstep_star_corestep_star in Steps2.
    eapply corestep_star_rdonly; eassumption.
Qed.  

End Mini_simulation_injects. 
End Mini_simulation_inj. 

Definition genv_next_eq {F1 V1 F2 V2: Type}
        (g1 : Genv.t F1 V1)
        (g2 : Genv.t F2 V2) := Genv.genv_next g1 = Genv.genv_next g2.

Module Mini_simulation_ext. 
Section Mini_simulation_extends. 
Context
  {F1 V1 C1 F2 V2 C2 : Type}
  (Sem1 : @EffectSem (Genv.t F1 V1) C1)
  (Sem2 : @EffectSem (Genv.t F2 V2) C2)
  (ge1 : Genv.t F1 V1)
  (ge2 : Genv.t F2 V2).

  Record Mini_simulation_extend :=
  { core_data : Type;

    match_state : core_data -> C1 -> mem -> (block -> bool) -> C2 -> mem -> Prop;
    core_ord : core_data -> core_data -> Prop;
    core_ord_wf : well_founded core_ord;

    senvs_dom_eq : Senv.equiv ge1 ge2 /\ genv_next_eq ge1 ge2;

    match_localblocks: forall d c1 m1 L c2 m2,  match_state d c1 m1 L c2 m2 -> 
      forall b, L b = true -> (Mem.valid_block m1 b /\ Mem.valid_block m2 b);

    match_validblocks: forall d c1 m1 L c2 m2,  match_state d c1 m1 L c2 m2 -> 
      forall b, Mem.valid_block m1 b <-> Mem.valid_block m2 b;

    (*ginfo_preserved : (*gvar_infos_eq ge1 ge2 /\*) findsymbols_preserved ge1 ge2;*)

    match_genv : forall d c1 m1 L c2 m2 (MC : match_state d c1 m1 L c2 m2),
      symbols_inject (Mem.flat_inj (Mem.nextblock m1)) ge1 ge2 /\
      meminj_preserves_globals ge1 (Mem.flat_inj (Mem.nextblock m1)) /\
      (forall b, isGlobalBlock ge1 b = true -> Mem.valid_block m1 b);

    core_initial : forall v vals1 c1 m1 vals2 m2,
       initial_core Sem1 ge1 v vals1 = Some c1 ->
       Forall2 Val.lessdef vals1 vals2 ->
       Mem.extends m1 m2 ->
       meminj_preserves_globals ge1 (Mem.flat_inj (Mem.nextblock m1)) ->
       symbols_inject (Mem.flat_inj (Mem.nextblock m1)) ge1 ge2 ->
       (*globalfunction_ptr_inject ge1 j -> MINI:MAYBE DON'T REMOVE THIS??*)
       mem_respects_readonly ge1 m1 -> mem_respects_readonly ge2 m2 ->
       exists cd, exists c2,
            initial_core Sem2 ge2 v vals2 = Some c2 /\
            match_state cd c1 m1 (fun b => false) c2 m2;

    effcore_diagram : forall st1 m1 st1' m1' U1, 
      effstep Sem1 ge1 U1 st1 m1 st1' m1' ->
        forall cd st2 m2 L,
      match_state cd st1 m1 L st2 m2 ->
      exists st2', exists m2', exists cd', exists L',

        L' = (fun b : block => L b || freshblock m1 m1' b) /\
        L' = (fun b : block => L b || freshblock m2 m2' b) /\

        match_state cd' st1' m1' L' st2' m2' /\
        exists U2,              
          (effstep_plus Sem2 ge2 U2 st2 m2 st2' m2' \/
            (effstep_star Sem2 ge2 U2 st2 m2 st2' m2' /\ core_ord cd' cd)) /\
          (forall b ofs (Ub: U2 b ofs = true),
            L b = true \/ U1 b ofs = true);

    core_halted : 
      forall cd st1 m1 st2 L m2 v1,
        match_state cd st1 m1 L st2 m2 ->
        halted Sem1 st1 = Some v1 -> 
        exists v2, Val.lessdef v1 v2 /\
            mem_respects_readonly ge1 m1 /\ 
            mem_respects_readonly ge2 m2 /\
            halted Sem2 st2 = Some v2 /\
            Mem.extends m1 m2;

    core_at_external : 
      forall cd st1 m1 L st2 m2 e vals1 efsig,
        match_state cd st1 m1 L st2 m2 ->
        at_external Sem1 st1 = Some (e,efsig,vals1) ->
        Mem.extends m1 m2 /\ mem_respects_readonly ge1 m1 /\ mem_respects_readonly ge2 m2 /\
        exists vals2,
          Forall2 Val.lessdef vals1 vals2 /\
          at_external Sem2 st2 = Some (e,efsig,vals2)
          (*maybe add /\ efsig = ef_sig e?*);

    core_after_external :
      forall cd st1 m1 L st2 m2 e vals1 vals2 efsig
      (MatchMu: match_state cd st1 m1 L st2 m2)
      (AtExtSrc: at_external Sem1 st1 = Some (e,efsig,vals1))
      (AtExtTgt: at_external Sem2 st2 = Some (e,efsig,vals2))
      (ARGSLD: Forall2 Val.lessdef vals1 vals2),
     forall ret1 m1' ret2 m2'
        (HasTy1: Val.has_type ret1 (proj_sig_res efsig))
        (HasTy2: Val.has_type ret2 (proj_sig_res efsig))

        (MEXT': Mem.extends m1' m2')
        (RVLD: Val.lessdef ret1 ret2) 

        (FwdSrc: mem_forward m1 m1') (FwdTgt: mem_forward m2 m2')
        (RDO1: RDOnly_fwd m1 m1' (ReadOnlyBlocks ge1))
        (RDO2: RDOnly_fwd m2 m2' (ReadOnlyBlocks ge2))

        (UnchTgt: Mem.unchanged_on (o_o_reach (Mem.flat_inj (Mem.nextblock m1)) L m1) m2 m2'),
        (*TAKES role of Mem.unchanged_on (loc_out_of_bounds m1) m2 m2',
          ie that (local!) spill-locations didn't change*)

        exists cd' st1' st2',
          after_external Sem1 (Some ret1) st1 = Some st1' /\
          after_external Sem2 (Some ret2) st2 = Some st2' /\
          match_state cd' st1' m1' L st2' m2'

}.

End Mini_simulation_extends.

Implicit Arguments Mini_simulation_extend [[F1] [V1] [C1] [F2] [V2] [C2]].

End Mini_simulation_ext.


