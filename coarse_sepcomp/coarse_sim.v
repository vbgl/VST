Require Import compcert.lib.Coqlib.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import compcert.common.Events.
Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.

Require Import VST.coarse_sepcomp.coarse_defs.
Require Import VST.coarse_sepcomp.coarse_semantics.

Module SM_simulationINJ. Section SharedMemory_simulation_inject.

(** Simulations are parameterized by a source interaction semantics
    [Sem1] and by a target interaction semantics [Sem2]. *)

(** [ge1] and [ge2] are the global environments associated with [Sem1] and
    [Sem2] respectively. *)

Context
  {F1 V1 C1 F2 V2 C2 : Type}
  (Sem1 : @MemSem (Genv.t F1 V1) C1)
  (Sem2 : @MemSem (Genv.t F2 V2) C2)
  (ge1 : Genv.t F1 V1)
  (ge2 : Genv.t F2 V2).

Record SM_simulation_inject := {
  (** Because we're doing csteps, we don't need coredata here any longer (individual phases may still need it).
      Instead of using structured simulations, we enhance the matchstate relation by blockset LS and LT (local blocks in SRC/TGT)*)
  match_state :  meminj -> (Blockset * Blockset) -> C1 -> mem -> C2 -> mem -> Prop

; match_ext: (option val -> option C1) -> (option val -> option C2) -> typ ->
             meminj -> (Blockset * Blockset) -> C1 -> list val -> mem -> C2 -> list val -> mem -> Prop

; match_ext_state: forall after1 after2 tp j LST c1 args1 m1 c2 args2 m2
                         (MA: match_ext after1 after2 tp j LST c1 args1 m1 c2 args2 m2),
                   match_state j LST c1 m1 c2 m2 /\ Forall2 (val_inject j) args1 args2

; match_ext_idle: forall after1 after2 tp j LS LT c1 args1 m1 c2 args2 m2
                         (MA: match_ext after1 after2 tp j (LS, LT) c1 args1 m1 c2 args2 m2)
                         j' m1' m2'
                         (GSep: globals_separate ge2 j j')
                         (INC: inject_incr j j') (SEP: esep m1 j j' m2 LT)
                         (Jvalid': forall b1 b2 d, j' b1 = Some(b2,d) -> Mem.valid_block m1' b1 /\ Mem.valid_block m2' b2)
                         (MemInj: Mem.inject j' m1' m2')
                         (FwdSrc: forward ge1 m1 m1') (FwdTgt: forward ge2 m2 m2')

                         (UnchSrc: Mem.unchanged_on (fun b z => LS b = true /\ j b = None) m1 m1') (*local unmapped*)
                         (UnchTgt: Mem.unchanged_on (fun b z => LT b = true /\ loc_out_of_reach j m1 b z) m2 m2'), (*local spills*)
                  match_ext after1 after2 tp j' (LS, LT) c1 args1 m1' c2 args2 m2'

; match_ext_resume: forall after1 after2 tp j LST c1 args1 m1 c2 args2 m2
                           (MA: match_ext after1 after2 tp j LST c1 args1 m1 c2 args2 m2)
                           ret1 ret2
                           (HasTy1: Val.has_type ret1 tp)
                           (HasTy2: Val.has_type ret2 tp)
                           (RValInj: val_inject j ret1 ret2),
                    exists st1', exists st2',
                      after1 (Some ret1) = Some st1' /\ after2 (Some ret2) = Some st2' /\
                      match_state j LST st1' m1 st2' m2

  (** ok to impose now as we have coarse-steps*)
; match_inject: forall j c1 m1 c2 m2 L,
    match_state j L c1 m1 c2 m2 -> Mem.inject j m1 m2 

  (** locations in LS are valid in m1*)
; match_LS: forall j c1 m1 c2 m2 LS LT,
    match_state j (LS, LT) c1 m1 c2 m2 -> forall b, LS b = true -> Mem.valid_block m1 b

  (** locations in LT are valid in m2*)
; match_LT: forall j c1 m1 c2 m2 LS LT,
    match_state j (LS, LT) c1 m1 c2 m2 -> forall b, LT b = true -> Mem.valid_block m2 b

  (** mapping respects locality classification*)
; match_jL: forall j c1 m1 c2 m2 LS LT,
    match_state j (LS, LT) c1 m1 c2 m2 -> forall b1 b2 d (J: j b1 =Some(b2,d)),
    LS b1 = LT b2

; match_genv:
    forall j c1 m1 c2 m2 LS LT, match_state j (LS,LT) c1 m1 c2 m2 ->
    globals_valid ge1 m1 /\ globals_valid ge2 m2 /\ globals_preserved ge1 ge2 j /\
    mem_respects_readonly ge1 m1 /\ mem_respects_readonly ge2 m2 /\
    (forall b1 b2 d (J: j b1 = Some(b2,d)), ReadOnlyBlocks ge1 b1 = true <-> ReadOnlyBlocks ge2 b2 = true) /\
    (forall b, isGlobalBlock ge1 b = true -> LS b = false) 

  (** The blocks in the domain/range of [j] are valid in [m1]/[m2]. *)
; match_validblocks: forall j c1 m1 c2 m2 L,
    match_state j L c1 m1 c2 m2 ->
    forall b1 b2 d, j b1 = Some(b2,d) -> Mem.valid_block m1 b1 /\ Mem.valid_block m2 b2

  (** The clause that relates initial states. *)
; core_initial: forall v vals1 c1 m1 j vals2 m2,
    initial_core Sem1 0 ge1 m1 v vals1 = Some c1 ->
    Mem.inject j m1 m2 ->
    Forall2 (val_inject j) vals1 vals2 ->
      (*meminj_preserves_globals ge1 j -> globalfunction_ptr_inject ge1 j ->*)
      globals_valid ge1 m1 -> globals_valid ge2 m2 -> globals_preserved ge1 ge2 j ->
      mem_respects_readonly ge1 m1 -> mem_respects_readonly ge2 m2 ->
      (forall b1 b2 d, j b1 = Some(b2,d) -> Mem.valid_block m1 b1 /\ Mem.valid_block m2 b2) ->
    exists c2, initial_core Sem2 0 ge2 m2 v vals2 = Some c2
            /\ match_state j (fun b => false, fun b => false) c1 m1 c2 m2 

(** We combine former clauses core-diagram, at-after-external, and halted into a diagram for coarsesteps. *)
; coarsestep_diagram :
    forall j st1 m1 st2 m2 LS LT (Match: match_state j (LS, LT) st1 m1 st2 m2)
    R1 (Step: cstep Sem1 ge1 st1 m1 R1),
    match R1 with
        CSR_Ext c1 m1' (e, vals1, after1) => exists j',
          inject_incr j j' /\ isep m1 j j' m2 LT /\ globals_separate ge2 j j'
          /\ exists c2 m2' vals2 after2, cstep Sem2 ge2 st2 m2 (CSR_Ext c2 m2' (e, vals2, after2))
             /\ write_confined m1 m1' j LT m2 m2'
             /\ let LS' := fun b => LS b || freshblockB m1 m1' b in
                let LT' := fun b => LT b || freshblockB m2 m2' b in
                match_ext after1 after2 (proj_sig_res (AST.ef_sig e)) j' (LS', LT') c1 vals1 m1' c2 vals2 m2'
      | CSR_Ret c1 m1' v1 => exists j',
          inject_incr j j' /\ isep m1 j j' m2 LT /\ globals_separate ge2 j j'
          /\ exists c2 m2' v2, cstep Sem2 ge2 st2 m2 (CSR_Ret c2 m2' v2)
             /\ Mem.inject j' m1' m2'
             /\ write_confined m1 m1' j LT m2 m2'
             /\ val_inject j' v1 v2
      | CSR_Div mi1 => exists mi2, cstep Sem2 ge2 st2 m2 (CSR_Div mi2)
          /\ forall i, write_confined m1 (mi1 i) j LT m2 (mi2 i)
    end
}.

Lemma match_extcall_oneshot {SIM:SM_simulation_inject}: 
      forall after1 after2 tp j LS LT c1 args1 m1 c2 args2 m2
                         (MA: match_ext SIM after1 after2 tp j (LS, LT) c1 args1 m1 c2 args2 m2),
                  match_state SIM j (LS, LT) c1 m1 c2 m2 /\ Forall2 (val_inject j) args1 args2 /\
                  forall j' ret1 m1' ret2 m2'
                     (HasTy1: Val.has_type ret1 tp)
                     (HasTy2: Val.has_type ret2 tp)
                     (GSep: globals_separate ge2 j j')
                     (INC: inject_incr j j') (Esep: esep m1 j j' m2 LT) 
                     (MemInj: Mem.inject j' m1' m2')
                     (Jvalid': forall b1 b2 d, j' b1 = Some(b2,d) -> Mem.valid_block m1' b1 /\ Mem.valid_block m2' b2)
                     (RValInj: val_inject j' ret1 ret2)

                     (FwdSrc: forward ge1 m1 m1') (FwdTgt: forward ge2 m2 m2')

                     (UnchSrc: Mem.unchanged_on (fun b z => LS b = true /\ j b = None) m1 m1') (*local unmapped*)
                     (UnchTgt: Mem.unchanged_on (fun b z => LT b = true /\ loc_out_of_reach j m1 b z) m2 m2'), (*local spills*)

                  exists st1', exists st2',
                  after1 (Some ret1) = Some st1' /\ after2 (Some ret2) = Some st2' /\
                  match_state SIM j' (LS, LT) st1' m1' st2' m2'.
Proof. intros.
  destruct (match_ext_state SIM _ _ _ _ _ _ _ _ _ _ _ MA).
  split; [trivial | split; [trivial | intros]].
  exploit (match_ext_idle SIM _ _ _ _ _ _ _ _ _ _ _ _ MA); try eassumption. intros.
  eapply match_ext_resume; eassumption.
Qed.

End SharedMemory_simulation_inject.
End SM_simulationINJ. 

Module SM_simulationEXT.
Section SharedMemory_simulation_extend.

Context
  {F1 V1 C1 F2 V2 C2 : Type}
  (Sem1 : @MemSem (Genv.t F1 V1) C1)
  (Sem2 : @MemSem (Genv.t F2 V2) C2)
  (ge1 : Genv.t F1 V1)
  (ge2 : Genv.t F2 V2).

Record SM_simulation_extend := {
  match_state :  Blockset -> C1 -> mem -> C2 -> mem -> Prop

; match_ext: (option val -> option C1) -> (option val -> option C2) -> typ ->
              Blockset -> C1 -> list val -> mem -> C2 -> list val -> mem -> Prop

; match_ext_state: forall Res1 Res2 tp L c1 args1 m1 c2 args2 m2
                         (MA: match_ext Res1 Res2 tp L c1 args1 m1 c2 args2 m2),
                   match_state L c1 m1 c2 m2 /\ Forall2 Val.lessdef args1 args2

; match_ext_idle: forall Res1 Res2 tp L c1 args1 m1 c2 args2 m2
                         (MA: match_ext Res1 Res2 tp L c1 args1 m1 c2 args2 m2)
                         m1' m2'
                         (MemExt: Mem.extends m1' m2')
                         (FwdSrc: forward ge1 m1 m1') (FwdTgt: forward ge2 m2 m2')
                         (UnchTgt: Mem.unchanged_on (fun b z => L b = true /\ loc_out_of_bounds m1 b z) m2 m2'), (*local spills*)
                  match_ext Res1 Res2 tp L c1 args1 m1' c2 args2 m2'

; match_ext_resume: forall Res1 Res2 tp L c1 args1 m1 c2 args2 m2
                           (MA: match_ext Res1 Res2 tp L c1 args1 m1 c2 args2 m2)
                           ret1 ret2
                           (HasTy1: Val.has_type ret1 tp)
                           (HasTy2: Val.has_type ret2 tp)
                           (RValLD: Val.lessdef ret1 ret2),
                    exists st1', exists st2',
                      Res1 (Some ret1) = Some st1' /\ Res2 (Some ret2) = Some st2' /\
                      match_state L st1' m1 st2' m2

  (** ok to impose now as we have coarse-steps*)
; match_extends: forall c1 m1 c2 m2 L,
    match_state L c1 m1 c2 m2 -> Mem.extends m1 m2 

  (** locations in L are valid in m1*)
; match_L: forall c1 m1 c2 m2 L,
    match_state L c1 m1 c2 m2 -> forall b, L b = true -> Mem.valid_block m1 b

; match_genv: forall c1 m1 c2 m2 L, match_state L c1 m1 c2 m2 ->
    globals_valid ge1 m1 /\ globals_valid ge2 m2 /\ (*globals_preserved ge1 ge2 j /\*)
    mem_respects_readonly ge1 m1 /\ mem_respects_readonly ge2 m2 /\
    (forall b, ReadOnlyBlocks ge1 b = true <-> ReadOnlyBlocks ge2 b = true) /\
    (forall b, isGlobalBlock ge1 b = true -> isGlobalBlock ge2 b = true /\ L b = false) 

  (** The blocks in the domain/range of [j] are valid in [m1]/[m2]. *)
; match_validblocks: forall c1 m1 c2 m2 L,
    match_state L c1 m1 c2 m2 ->
    forall b, Mem.valid_block m1 b <-> Mem.valid_block m2 b

  (** The clause that relates initial states. *)
; core_initial: forall v vals1 c1 m1 vals2 m2,
      initial_core Sem1 0 ge1 m1 v vals1 = Some c1 ->
      Mem.extends m1 m2 ->
      Forall2 Val.lessdef vals1 vals2 ->
      (*meminj_preserves_globals ge1 j -> globalfunction_ptr_inject ge1 j ->*)
      globals_valid ge1 m1 -> globals_valid ge2 m2 -> (*globals_preserved ge1 ge2 j ->*)
      mem_respects_readonly ge1 m1 -> mem_respects_readonly ge2 m2 ->
    exists c2, initial_core Sem2 0 ge2 m2 v vals2 = Some c2
            /\ match_state (fun b => false) c1 m1 c2 m2 

(** We combine former clauses core-diagram, at-after-external, and halted into a diagram for coarsesteps. *)
; coarsestep_diagram: forall st1 m1 st2 m2 L
   (Match: match_state L st1 m1 st2 m2) R1 (Step: cstep Sem1 ge1 st1 m1 R1),
    match R1 with
        CSR_Ext c1 m1' (e, vals1, after1) => exists c2 m2' vals2 after2,
                 cstep Sem2 ge2 st2 m2 (CSR_Ext c2 m2' (e, vals2, after2))
              /\ write_confinedExt m1 m1' L m2 m2'
              /\ let L' := fun b => L b || freshblockB m1 m1' b in
                 match_ext after1 after2 (proj_sig_res (AST.ef_sig e)) L' c1 vals1 m1' c2 vals2 m2' 
      | CSR_Ret c1 m1' v1 => exists c2 m2' v2, 
             cstep Sem2 ge2 st2 m2 (CSR_Ret c2 m2' v2)
             /\ Mem.extends m1' m2'
             /\ write_confinedExt m1 m1' L m2 m2'
             /\ Val.lessdef v1 v2
      | CSR_Div mi1 => exists mi2,
              cstep Sem2 ge2 st2 m2 (CSR_Div mi2)
           /\ forall i, write_confinedExt m1 (mi1 i) L m2 (mi2 i)
    end
}.
End SharedMemory_simulation_extend.
End SM_simulationEXT. 

Module SM_simulationEQ.
Section SharedMemory_simulation_equality.
Context
  {F1 V1 C1 F2 V2 C2 : Type}
  (Sem1 : @MemSem (Genv.t F1 V1) C1)
  (Sem2 : @MemSem (Genv.t F2 V2) C2)
  (ge1 : Genv.t F1 V1)
  (ge2 : Genv.t F2 V2).

Record SM_simulation_equality := {
  match_state :  Blockset -> C1 -> mem -> C2 -> Prop

; match_ext: (option val -> option C1) -> (option val -> option C2) -> typ ->
              Blockset -> C1 -> list val -> mem -> C2 -> Prop

; match_ext_state: forall Res1 Res2 tp L c1 args1 m c2
                         (MA: match_ext Res1 Res2 tp L c1 args1 m c2),
                   match_state L c1 m c2

; match_ext_idle: forall Res1 Res2 tp L c1 args1 m c2
                         (MA: match_ext Res1 Res2 tp L c1 args1 m c2)
                         m' (FwdSrc: forward ge1 m m') (FwdTgt: forward ge2 m m'),
                  match_ext Res1 Res2 tp L c1 args1 m' c2

; match_ext_resume: forall Res1 Res2 tp L c1 args1 m c2
                           (MA: match_ext Res1 Res2 tp L c1 args1 m c2)
                           ret   (HasT1: Val.has_type ret tp),
                    exists st1', exists st2',
                      Res1 (Some ret) = Some st1' /\ Res2 (Some ret) = Some st2' /\
                      match_state L st1' m st2'

  (** locations in L are valid in m1*)
; match_L: forall c1 m c2 L,
    match_state L c1 m c2 -> forall b, L b = true -> Mem.valid_block m b

; match_genv: forall c1 m c2 L, match_state L c1 m c2 ->
    globals_valid ge1 m /\ globals_valid ge2 m /\
    mem_respects_readonly ge1 m /\ mem_respects_readonly ge2 m /\
    (forall b, isGlobalBlock ge1 b = true -> L b = false) 

; eq_globals:  isGlobalBlock ge1 = isGlobalBlock ge2

; eq_readonly: forall b, ReadOnlyBlocks ge1 b = true <-> ReadOnlyBlocks ge2 b = true

  (** The clause that relates initial states. *)
; core_initial: forall v vals c1 m,
      initial_core Sem1 0 ge1 m v vals = Some c1 ->
      (*meminj_preserves_globals ge1 j -> globalfunction_ptr_inject ge1 j ->*)
      globals_valid ge1 m -> globals_valid ge2 m -> (*globals_preserved ge1 ge2 j ->*)
      mem_respects_readonly ge1 m -> mem_respects_readonly ge2 m ->
    exists c2, initial_core Sem2 0 ge2 m v vals = Some c2
            /\ match_state (fun b => false) c1 m c2 


(** We combine former clauses core-diagram, at-after-external, and halted into a diagram for coarsesteps. *)
; coarsestep_diagram: forall st1 m st2 L
    (Match: match_state L st1 m st2) R1 (Step: cstep Sem1 ge1 st1 m R1),
    match R1 with
        CSR_Ext c1 m' (e, vals, after1) => exists c2 after2,
                 cstep Sem2 ge2 st2 m (CSR_Ext c2 m' (e, vals, after2))
              /\ let L' := fun b => L b || freshblockB m m' b in
                 match_ext after1 after2 (proj_sig_res (AST.ef_sig e)) L' c1 vals m' c2 
      | CSR_Ret c1 m' v => exists c2, 
             cstep Sem2 ge2 st2 m (CSR_Ret c2 m' v)
      | CSR_Div mi => cstep Sem2 ge2 st2 m (CSR_Div mi)
    end
}.
End SharedMemory_simulation_equality.
End SM_simulationEQ. 
