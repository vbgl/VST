Require Import Coq.Bool.Bool.

Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.lib.Integers.

Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import compcert.common.Events.
Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.

Require Import VST.msl.Axioms.

Require Import VST.sepcomp.mem_lemmas.
Require Import VST.sepcomp.semantics.
Require Import VST.sepcomp.effect_semantics.
Require Import VST.sepcomp.structured_injections.
Require Import VST.sepcomp.reach.

Definition MST_locally_allocated {C1 C2} (mu mu' : SM_Injection) (m1 m2 : mem) 
           (A1: @MidStepTrackResult C1) (A2: @MidStepTrackResult C2):=
match A1, A2 with
  MST_Ext _ m1' _ _ _, MST_Ext _ m2' _ _ _ => sm_locally_allocated mu mu' m1 m2 m1' m2'
| MST_Ret _ m1' _ _,  MST_Ret _ m2' _ _ => sm_locally_allocated mu mu' m1 m2 m1' m2'
| _, _ => True
end.

Definition confined W1 W2 mu :=
  forall b2 z (Eb2: extBlocksTgt mu b2 = true),
         W2 b2 z ->
         (exists b1 d, foreign_of mu b1 = Some(b2,d) /\ W1 b1 (z-d)).

(*This definition aims to be the mirrored version of local_out_of_reach.
  In particular, including mem_unchange_on (extern_out_of_reach nu m1) m2 m2' in 
  match_midstep should (fingers crossed) suffice for establishing the caller's
  condition mem_unchanged_on (local_out_of_reach nu m1) m2 m2' 
  of clause matchafter_external*)
Definition extern_out_of_reach mu (m : mem) (b : block) (ofs : Z): Prop :=
  extBlocksTgt mu b = true /\
  (forall b0 delta, extern_of mu b0 = Some (b, delta) ->
                  (~ Mem.perm m b0 (ofs - delta) Max Nonempty \/
                   frgnBlocksSrc mu b0 = false)).

Lemma confined_unch (W1 W2:block -> Z -> Prop) mu (m1 m2 m2':mem) (SMV:sm_valid mu m1 m2) 
      (Fwd: mem_forward m2 m2') (WD:SM_wd mu) (C:confined W1 W2 mu)
      (HW1: forall b z, W1 b z -> Mem.valid_block m1 b -> Mem.perm m1 b z Cur Writable):
      Mem.unchanged_on (fun b z => ~ W2 b z) m2 m2' ->
      Mem.unchanged_on (extern_out_of_reach mu m1) m2 m2'.
Proof. constructor.
apply mem_forward_nextblock; eassumption.
{ intros b2 z k p [E1 E3(*[E2 E3]*)] V.
  apply H; trivial. intros N.
  destruct (C b2 z E1 N) as [b1 [d [FRG Perm]]].
  destruct (E3 b1 d); [ apply foreign_in_extern; trivial |  | apply frgnBlocksSrc_false_foreign_None in H0; congruence].
  apply H0. eapply Mem.perm_implies. eapply Mem.perm_cur. apply (HW1 _ _ Perm).
  apply SMV. eapply foreign_DomRng; eauto. constructor. }
{ intros b2 z [E1 E3(*[E2 E3]*)] P.
  apply H; trivial. intros N.
  destruct (C b2 z E1 N) as [b1 [d [FRG Perm]]].
  destruct (E3 b1 d); [ apply foreign_in_extern; trivial |  | apply frgnBlocksSrc_false_foreign_None in H0; congruence].
  apply H0. eapply Mem.perm_implies. eapply Mem.perm_cur. apply (HW1 _ _ Perm).
  apply SMV. eapply foreign_DomRng; eauto. constructor. }
Qed.

(*Cosmetic improvement wrt compcomp: hide the replace_locals stuff in this definition*)
Definition publish mu m1 vals1 m2 vals2 :=
  replace_locals mu 
         (fun b => locBlocksSrc mu b && REACH m1 (exportedSrc mu vals1) b) 
         (fun b => locBlocksTgt mu b && REACH m2 (exportedTgt mu vals2) b).

Module SM_simulation. Section SharedMemory_simulation_inject.

Context
  {F1 V1 C1 F2 V2 C2 : Type}
  (Sem1 : @EffectSem (Genv.t F1 V1) C1)
  (Sem2 : @EffectSem (Genv.t F2 V2) C2)
  (ge1 : Genv.t F1 V1)
  (ge2 : Genv.t F2 V2).

(*matchstate will be instantiated with match_state cd below*)
Definition MST_relate matchstate mu (A: @MidStepTrackResult C1)
    (B: @MidStepTrackResult C2):=
match A, B with
  MST_Ext c1 m1 W1 f1 vals1, MST_Ext c2 m2 W2 f2 vals2 =>
       (*No need to require matchstate mu c1 m1 c2 m2 (maybe...)*)
       sm_valid mu m1 m2 /\ SM_wd mu /\
       Mem.inject (as_inj mu) m1 m2 (*probably need this to calculate/relate REACH-closures correctly*)
       /\ f1=f2
       /\ mem_respects_readonly ge1 m1 /\ mem_respects_readonly ge2 m2
       /\ Forall2 (val_inject (restrict (as_inj mu) (vis mu))) vals1 vals2
       /\ let nu := publish mu m1 vals1 m2 vals2
          in matchstate nu c1 m1 c2 m2 /\ Mem.inject (shared_of nu) m1 m2
| MST_Ret c1 m1 W1 v1, MST_Ret c2 m2 W2 v2 => 
       sm_valid mu m1 m2 /\ SM_wd mu /\
        Mem.inject (as_inj mu) m1 m2
        /\ mem_respects_readonly ge1 m1 /\ mem_respects_readonly ge2 m2
        /\ val_inject (restrict (as_inj mu) (vis mu)) v1 v2
| MST_Div W1, MST_Div W2 => True 
| _, _ => False
end.

Record SM_simulation_inject :=
{ core_data : Type
; match_state : core_data -> SM_Injection -> C1 -> mem -> C2 -> mem -> Prop
; core_ord : core_data -> core_data -> Prop
; core_ord_wf : well_founded core_ord

; match_sm_wd :
    forall d mu c1 m1 c2 m2,
    match_state d mu c1 m1 c2 m2 -> SM_wd mu

; genvs_dom_eq : genvs_domain_eq ge1 ge2

  (** The global environments also associate same info with global blocks and
      preserve find_var. These conditions are used for in the transitivity proof,
      to establish mem_respects_readonly for the intermediate memory and globalenv. *)
(*Still Needed?
; ginfo_preserved : gvar_infos_eq ge1 ge2 /\ findsymbols_preserved ge1 ge2*)


; match_genv :
    forall d mu c1 m1 c2 m2 (MC : match_state d mu c1 m1 c2 m2),
    meminj_preserves_globals ge1 (extern_of mu) /\
    (forall b, isGlobalBlock ge1 b = true -> frgnBlocksSrc mu b = true)

; match_visible :
    forall d mu c1 m1 c2 m2,
    match_state d mu c1 m1 c2 m2 ->
    REACH_closed m1 (vis mu)
(*
; match_restrict :
    forall d mu c1 m1 c2 m2 X,
    match_state d mu c1 m1 c2 m2 ->
    (forall b, vis mu b = true -> X b = true) ->
    REACH_closed m1 X ->
    match_state d (restrict_sm mu X) c1 m1 c2 m2*)

; match_validblocks :
    forall d mu c1 m1 c2 m2,
    match_state d mu c1 m1 c2 m2 ->
    sm_valid mu m1 m2


; core_initial :
    forall v vals1 c1 m1 j vals2 m2 DomS DomT,
    initial_core Sem1 0 ge1 v vals1 = Some c1 ->
    Mem.inject j m1 m2 ->
    Forall2 (val_inject j) vals1 vals2 ->
    meminj_preserves_globals ge1 j ->

    (*the next two conditions are required to guarantee initialSM_wd*)
    (forall b1 b2 d, j b1 = Some (b2, d) ->
      DomS b1 = true /\ DomT b2 = true) ->
    (forall b,
      REACH m2 (fun b' => isGlobalBlock ge2 b' || getBlocks vals2 b') b=true ->
      DomT b = true) ->

    (*the next two conditions ensure the initialSM satisfies sm_valid*)
    (forall b, DomS b = true -> Mem.valid_block m1 b) ->
    (forall b, DomT b = true -> Mem.valid_block m2 b) ->

    exists cd, exists c2,
    initial_core Sem2 0 ge2 v vals2 = Some c2
    /\ match_state cd
         (initial_SM DomS DomT
           (REACH m1 (fun b => isGlobalBlock ge1 b || getBlocks vals1 b))
           (REACH m2 (fun b => isGlobalBlock ge2 b || getBlocks vals2 b)) j)
         c1 m1 c2 m2

(*Unifies corestep_diagram (incl step-star stuff), core_atExternal, and core_halted*)
; match_midstep :
    forall d mu c1 m1 c2 m2 A1,
    match_state d mu c1 m1 c2 m2 ->
    midstepT Sem1 ge1 c1 m1 A1 ->
    exists A2 cd' mu', 
      midstepT Sem2 ge2 c2 m2 A2
      /\ intern_incr mu mu'
(*      /\ globals_separate ge2 mu mu'?? still neeeded?*)
      /\ MST_locally_allocated mu mu' m1 m2 A1 A2 (*replaces sm_locally_allocated mu mu' m1 m2 m1' m2'*)
      /\ MST_relate (match_state cd') mu' A1 A2
      /\ confined (Wset A1) (Wset A2) mu (*using mu' here would be equivalent, thanks to intern_incr mu mu'*)
      (*TODO: do we actually still need the indices cd/cd'? If yes, probably insert core_ord cd' cd clause*)

(*
; effcore_diagram :
    forall st1 m1 st1' m1' U1,
    effstep Sem1 ge1 U1 st1 m1 st1' m1' ->
    forall cd st2 mu m2,
    match_state cd mu st1 m1 st2 m2 ->
    exists st2', exists m2', exists cd', exists mu',
      intern_incr mu mu'
      /\ sm_inject_separated mu mu' m1 m2
      /\ sm_locally_allocated mu mu' m1 m2 m1' m2'
      /\ match_state cd' mu' st1' m1' st2' m2'
      /\ exists U2,
          ((effstep_plus Sem2 ge2 U2 st2 m2 st2' m2' \/
            (effstep_star Sem2 ge2 U2 st2 m2 st2' m2' /\
             core_ord cd' cd)) /\
         forall
           (UHyp: forall b1 z, U1 b1 z = true -> vis mu b1 = true)
           b ofs (Ub: U2 b ofs = true),
           visTgt mu b = true
           /\ (locBlocksTgt mu b = false ->
               exists b1 delta1,
                 foreign_of mu b1 = Some(b,delta1)
                 /\ U1 b1 (ofs-delta1) = true
                 /\ Mem.perm m1 b1 (ofs-delta1) Max Nonempty))


; core_halted :
    forall cd mu c1 m1 c2 m2 v1,
    match_state cd mu c1 m1 c2 m2 ->
    halted Sem1 c1 = Some v1 ->
    exists v2,
    Mem.inject (as_inj mu) m1 m2
    /\ val_inject (restrict (as_inj mu) (vis mu)) v1 v2
    /\ halted Sem2 c2 = Some v2


; core_at_external :
    forall cd mu c1 m1 c2 m2 e vals1,
    match_state cd mu c1 m1 c2 m2 ->
    at_external Sem1 c1 = Some (e,vals1) ->
    Mem.inject (as_inj mu) m1 m2
    /\ exists vals2,
       Forall2 (val_inject (restrict (as_inj mu) (vis mu))) vals1 vals2
       /\ at_external Sem2 c2 = Some (e,vals2)

    /\ forall
       (pubSrc' pubTgt' : block -> bool)
       (pubSrcHyp : pubSrc' =
                  (fun b : block =>
                  locBlocksSrc mu b && REACH m1 (exportedSrc mu vals1) b))
       (pubTgtHyp: pubTgt' =
                  (fun b : block =>
                  locBlocksTgt mu b && REACH m2 (exportedTgt mu vals2) b))
       nu (Hnu: nu = (replace_locals mu pubSrc' pubTgt')),
       match_state cd nu c1 m1 c2 m2
       /\ Mem.inject (shared_of nu) m1 m2
*)

(*No change here*)
; eff_after_external:
    forall cd mu st1 st2 m1 e vals1 m2 vals2 e'
      (MemInjMu: Mem.inject (as_inj mu) m1 m2)
      (MatchMu: match_state cd mu st1 m1 st2 m2)
      (AtExtSrc: at_external Sem1 st1 = Some (e,vals1))

        (* We include the clause AtExtTgt to ensure that vals2 is
         uniquely determined. We have e=e' and ef_sig=ef_sig' by the
         at_external clause, but omitting the hypothesis AtExtTgt
         would result in in 2 not necesssarily equal target argument
         lists in language 3 in the transitivity, as val_inject is not
         functional in the case where the left value is Vundef. (And
         we need to keep ValInjMu since vals2 occurs in pubTgtHyp) *)

      (AtExtTgt: at_external Sem2 st2 = Some (e',vals2))
      (ValInjMu: Forall2 (val_inject (restrict (as_inj mu) (vis mu))) vals1 vals2)

      pubSrc'
      (pubSrcHyp:
         pubSrc'
         = (fun b => locBlocksSrc mu b && REACH m1 (exportedSrc mu vals1) b))

      pubTgt'
      (pubTgtHyp:
         pubTgt'
         = fun b => locBlocksTgt mu b && REACH m2 (exportedTgt mu vals2) b)

      nu (NuHyp: nu = replace_locals mu pubSrc' pubTgt'),

      forall nu' ret1 m1' ret2 m2'
        (HasTy1: Val.has_type ret1 (proj_sig_res (AST.ef_sig e)))
        (HasTy2: Val.has_type ret2 (proj_sig_res (AST.ef_sig e')))
        (INC: extern_incr nu nu')
        (SEP: sm_inject_separated nu nu' m1 m2)

        (WDnu': SM_wd nu') (SMvalNu': sm_valid nu' m1' m2')

        (MemInjNu': Mem.inject (as_inj nu') m1' m2')
        (RValInjNu': val_inject (as_inj nu') ret1 ret2)

        (FwdSrc: mem_forward m1 m1') (FwdTgt: mem_forward m2 m2')

        frgnSrc'
        (frgnSrcHyp:
           frgnSrc'
           = fun b => DomSrc nu' b &&
                      (negb (locBlocksSrc nu' b) &&
                       REACH m1' (exportedSrc nu' (ret1::nil)) b))

        frgnTgt'
        (frgnTgtHyp:
           frgnTgt'
           = fun b => DomTgt nu' b &&
                      (negb (locBlocksTgt nu' b) &&
                       REACH m2' (exportedTgt nu' (ret2::nil)) b))

        mu' (Mu'Hyp: mu' = replace_externs nu' frgnSrc' frgnTgt')

         (UnchPrivSrc:
            Mem.unchanged_on (fun b ofs =>
              locBlocksSrc nu b = true /\
              pubBlocksSrc nu b = false) m1 m1')

         (UnchLOOR: Mem.unchanged_on (local_out_of_reach nu m1) m2 m2'),

        exists cd', exists st1', exists st2',
          after_external Sem1 (Some ret1) st1 = Some st1' /\
          after_external Sem2 (Some ret2) st2 = Some st2' /\
          match_state cd' mu' st1' m1' st2' m2' }.

Lemma midstep (SIM:SM_simulation_inject):
    forall d mu c1 m1 c2 m2 c1' m1' W1 f1 vals1,
    match_state SIM d mu c1 m1 c2 m2 ->
    midstepT Sem1 ge1 c1 m1 (MST_Ext c1' m1' W1 f1 vals1) ->
    exists A2 cd' mu' c2' m2' W2 f2 vals2, 
      A2 = MST_Ext c2' m2' W2 f2 vals2 /\
      at_external Sem1 c1' = Some (f1,vals1) /\ at_external Sem2 c2' = Some (f2,vals2)  /\
      midstepT Sem2 ge2 c2 m2 A2
      /\ intern_incr mu mu'
(*      /\ globals_separate ge2 mu mu'?? still neeeded?*)
      /\ MST_locally_allocated mu mu' m1 m2 (MST_Ext c1' m1' W1 f1 vals1)  A2
      (*/\ MST_relate (match_state SIM cd') mu' A1 A2*)
      /\ confined (Wset (MST_Ext c1' m1' W1 f1 vals1)) (Wset A2) mu
      /\ sm_valid mu' m1' m2' /\ SM_wd mu' /\
       Mem.inject (as_inj mu') m1' m2' (*probably need this to calculate/relate REACH-closures correctly*)
       /\ f1=f2
       /\ mem_respects_readonly ge1 m1' /\ mem_respects_readonly ge2 m2'
       /\ Forall2 (val_inject (restrict (as_inj mu') (vis mu'))) vals1 vals2
       /\ let nu := publish mu' m1' vals1 m2' vals2
          in match_state SIM cd' nu c1' m1' c2' m2' /\ Mem.inject (shared_of nu) m1' m2'.
Proof. intros. exploit match_midstep; eauto.
 intros [A2 [cd' [mu' [STEP2 [INC [ALLOC [REL CONF]]]]]]]. simpl in *.
 exists A2, cd', mu'.
 destruct A2; try contradiction. simpl in *.
 exists c, m, b, e, l.
 inv H0. inv STEP2; simpl in *. intuition.
  econstructor; trivial.
Print Mem.mem_inj.
Print compcert.common.Memory.Mem.meminj_no_overlap.
Definition MST_rel matchstate mu (A: @MidStepTrackResult C1)
    (B: @MidStepTrackResult C2):=
match A, B with
  MST_Ext c1 m1 W1 f1 vals1, MST_Ext c2 m2 W2 f2 vals2 =>
       sm_valid mu m1 m2 /\ SM_wd mu /\ f1=f2
       /\ mem_respects_readonly ge1 m1 /\ mem_respects_readonly ge2 m2
       /\ Forall2 (val_inject (shared_of mu)) vals1 vals2
       /\ matchstate mu c1 m1 c2 m2
       /\ Mem.inject (shared_of mu) m1 m2
       (*maybe not needed/\ Mem.inject (as_inj mu) m1 m2*)
| MST_Ret c1 m1 W1 v1, MST_Ret c2 m2 W2 v2 => 
       sm_valid mu m1 m2 /\ SM_wd mu /\
        Mem.inject (shared_of mu) m1 m2
        /\ mem_respects_readonly ge1 m1 /\ mem_respects_readonly ge2 m2
        /\ val_inject (shared_of mu) v1 v2
| MST_Div W1, MST_Div W2 => True 
| _, _ => False
end.

(*Abstract the replace_locals stuff- probably means the individial phase
proofs will now need to do this, incl maintaining REACH closure*)
Definition pubincr mu PS PT mu' :=
local_of mu = local_of mu' /\
extern_of mu = extern_of mu' /\
locBlocksSrc mu = locBlocksSrc mu' /\
locBlocksTgt mu = locBlocksTgt mu' /\
pubBlocksSrc mu' = (fun b => pubBlocksSrc mu b || PS b) /\
pubBlocksTgt mu' = (fun b => pubBlocksTgt mu b || PT b) /\
frgnBlocksSrc mu = frgnBlocksSrc mu' /\
frgnBlocksTgt mu = frgnBlocksTgt mu' /\
extBlocksSrc mu = extBlocksSrc mu' /\ extBlocksTgt mu = extBlocksTgt mu'.

Definition frgnincr mu FS FT mu' :=
local_of mu = local_of mu' /\
extern_of mu = extern_of mu' /\
locBlocksSrc mu = locBlocksSrc mu' /\
locBlocksTgt mu = locBlocksTgt mu' /\
pubBlocksSrc mu = pubBlocksSrc mu' /\
pubBlocksTgt mu = pubBlocksTgt mu' /\
frgnBlocksSrc mu' = (fun b => frgnBlocksSrc mu b || FS b) /\
frgnBlocksTgt mu' = (fun b => frgnBlocksTgt mu b || FT b) /\
extBlocksSrc mu = extBlocksSrc mu' /\ 
extBlocksTgt mu = extBlocksTgt mu'.

(*eliminates core_data from SM_simulation_inject -- this is now handled by the cores*)
(*But attempt to push replace_locals to phases fails in transitivity proof requires
that pubTgt2 implies pubSrc3 etc, which may fail if they the two phases make too many
/ different blocks public. Need to do exactly REACH m (extported mu vals)*)
Record Simple_simulation_inject :=
{ Smatch_state : SM_Injection -> C1 -> mem -> C2 -> mem -> Prop
; Smatch_sm_wd :
    forall mu c1 m1 c2 m2,
    Smatch_state mu c1 m1 c2 m2 -> SM_wd mu

; Sgenvs_dom_eq : genvs_domain_eq ge1 ge2

  (** The global environments also associate same info with global blocks and
      preserve find_var. These conditions are used for in the transitivity proof,
      to establish mem_respects_readonly for the intermediate memory and globalenv. *)
(*Still Needed?
; ginfo_preserved : gvar_infos_eq ge1 ge2 /\ findsymbols_preserved ge1 ge2*)


; Smatch_genv :
    forall mu c1 m1 c2 m2 (MC : Smatch_state mu c1 m1 c2 m2),
    meminj_preserves_globals ge1 (extern_of mu) /\
    (forall b, isGlobalBlock ge1 b = true -> frgnBlocksSrc mu b = true)
(*
; Smatch_visible :
    forall mu c1 m1 c2 m2,
    Smatch_state mu c1 m1 c2 m2 ->
    REACH_closed m1 (vis mu)*)

; Smatch_validblocks :
    forall mu c1 m1 c2 m2,
    Smatch_state mu c1 m1 c2 m2 ->
    sm_valid mu m1 m2

; Score_initial :
    forall v vals1 c1 m1 j vals2 m2 DomS DomT,
    initial_core Sem1 0 ge1 v vals1 = Some c1 ->
    Mem.inject j m1 m2 ->
    Forall2 (val_inject j) vals1 vals2 ->
    meminj_preserves_globals ge1 j ->

    (*the next two conditions are required to guarantee initialSM_wd*)
    (forall b1 b2 d, j b1 = Some (b2, d) ->
      DomS b1 = true /\ DomT b2 = true) ->
    (forall b,
      REACH m2 (fun b' => isGlobalBlock ge2 b' || getBlocks vals2 b') b=true ->
      DomT b = true) ->

    (*the next two conditions ensure the initialSM satisfies sm_valid*)
    (forall b, DomS b = true -> Mem.valid_block m1 b) ->
    (forall b, DomT b = true -> Mem.valid_block m2 b) ->

    exists c2,
    initial_core Sem2 0 ge2 v vals2 = Some c2
    /\ Smatch_state
         (initial_SM DomS DomT
           (REACH m1 (fun b => isGlobalBlock ge1 b || getBlocks vals1 b))
           (REACH m2 (fun b => isGlobalBlock ge2 b || getBlocks vals2 b)) j)
         c1 m1 c2 m2

(*Unifies corestep_diagram (incl step-star stuff), core_atExternal, and core_halted*)
; Smatch_midstep :
    forall mu c1 m1 c2 m2 A1,
    Smatch_state mu c1 m1 c2 m2 ->
    midstepT Sem1 ge1 c1 m1 A1 ->
    exists A2 mu' mu'' PS PT, 
      midstepT Sem2 ge2 c2 m2 A2
      /\ intern_incr mu mu' /\ pubincr mu' PS PT mu''
(*      /\ globals_separate ge2 mu mu'?? still neeeded?*)
      /\ MST_locally_allocated mu mu' m1 m2 A1 A2 (*replaces sm_locally_allocated mu mu' m1 m2 m1' m2'*)
      /\ MST_rel Smatch_state mu'' A1 A2
      /\ confined (Wset A1) (Wset A2) mu

; Saft_ext:
  forall mu c1 m1 W1 f1 vals1 c2 m2 W2 f2 vals2
     (REL: MST_rel Smatch_state mu (MST_Ext c1 m1 W1 f1 vals1) (MST_Ext c2 m2 W2 f2 vals2))
     (AtExtTgt: at_external Sem2 c2 = Some (f2,vals2))
     nu mu' ret1 m1' ret2 m2' FS FT
        (HasTy1: Val.has_type ret1 (proj_sig_res (AST.ef_sig f1)))
        (HasTy2: Val.has_type ret2 (proj_sig_res (AST.ef_sig f2)))
        (INC: extern_incr mu nu)
        (FINCR: frgnincr nu FS FT mu')
        (SEP: sm_inject_separated mu mu' m1 m2)

        (WDmu': SM_wd mu') (SMvalMu': sm_valid mu' m1' m2')

        (MemInjMu': Mem.inject (shared_of mu') m1' m2')
        (RValInjMu': val_inject (shared_of mu') ret1 ret2)

        (FwdSrc: mem_forward m1 m1') (FwdTgt: mem_forward m2 m2')

         (UnchPrivSrc:
            Mem.unchanged_on (fun b ofs =>
              locBlocksSrc mu b = true /\
              pubBlocksSrc mu b = false) m1 m1')

         (UnchLOOR: Mem.unchanged_on (local_out_of_reach mu m1) m2 m2'),

        exists st1', exists st2',
          after_external Sem1 (Some ret1) c1 = Some st1' /\
          after_external Sem2 (Some ret2) c2 = Some st2' /\
          Smatch_state mu' st1' m1' st2' m2' }.
(*
Require Import VST.sepcomp.semantics_lemmas.

Lemma core_diagram (SMI: SM_simulation_inject):
      forall st1 m1 st1' m1',
        corestep Sem1 ge1 st1 m1 st1' m1' ->
      forall cd st2 mu m2,
        match_state SMI cd mu st1 m1 st2 m2 ->
        exists st2', exists m2', exists cd', exists mu',
          intern_incr mu mu' /\
          sm_inject_separated mu mu' m1 m2 /\
          sm_locally_allocated mu mu' m1 m2 m1' m2' /\
          match_state SMI cd' mu' st1' m1' st2' m2' /\
          ((corestep_plus Sem2 ge2 st2 m2 st2' m2') \/
            corestep_star Sem2 ge2 st2 m2 st2' m2' /\
            core_ord SMI cd' cd).
Proof. intros.
apply effax2 in H. destruct H as [U1 H].
exploit (effcore_diagram SMI); eauto.
intros [st2' [m2' [cd' [mu' [INC [SEP [LOCALLOC
  [MST [U2 [STEP _]]]]]]]]]].
exists st2', m2', cd', mu'.
split; try assumption.
split; try assumption.
split; try assumption.
split; try assumption.
destruct STEP as [[n STEP] | [[n STEP] CO]];
  apply effstepN_corestepN in STEP.
left. exists n. assumption.
right; split; trivial. exists n. assumption.
Qed.
*)
End SharedMemory_simulation_inject.

End SM_simulation.
