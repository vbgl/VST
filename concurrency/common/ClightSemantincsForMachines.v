(* Clight SEmantics for Machines*)

(*
  We define event semantics for 
  - Clight_new: the core semantics defined by VST
  - Clightcore: the core semantics derived from 
    CompCert's Clight
*)

Require Import compcert.common.Memory.


Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.res_predicates.

(*IM using proof irrelevance!*)
Require Import ProofIrrelevance.

(* The concurrent machinery*)
Require Import VST.concurrency.common.core_semantics.
Require Import VST.concurrency.common.scheduler.
Require Import VST.concurrency.common.HybridMachineSig.
Require Import VST.concurrency.common.semantics.
Require Import VST.concurrency.common.lksize.
Require Import VST.concurrency.common.permissions.

(*Semantics*)
Require Import VST.veric.Clight_new.
Require Import VST.veric.Clightnew_coop.
Require Import VST.veric.Clight_core.
Require Import VST.veric.Clightcore_coop. 
Require Import VST.sepcomp.event_semantics.
Require Import VST.veric.Clight_sim.

Section ClightSEM.
  Definition F: Type := fundef.
  Definition V: Type := type.
  Definition G := genv.
  Definition C := corestate.
  Definition getEnv (g:G): Genv.t F V := genv_genv g.
  (* We might want to define this properly or
     factor the machines so we don't need events here. *)



  (** *Event semantics for Clight_new*)
  (* This should be a version of CLN_memsem annotated with memory events. *)
  Program Definition CLN_evsem ge : @EvSem C := {| msem := CLN_memsem ge |}.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.

  Lemma CLN_msem : forall ge, msem (CLN_evsem ge) = CLN_memsem ge.
  Proof. auto. Qed.

  Lemma CLN_step_decay: forall g c m tr c' m',
      event_semantics.ev_step (CLN_evsem g) c m tr c' m' ->
      decay m m'.
  Admitted.

  Lemma at_external_SEM_eq:
     forall ge c m, at_external (CLN_evsem ge) c m =
      match c with
      | State _ _ _ => None
      | ExtCall ef args _ _ _ _ => Some (ef, args)
      end.
  Proof. auto. Qed.

  Instance Clight_newSem ge : Semantics :=
    { semG := G; semC := C; semSem := CLN_evsem ge; the_ge := ge }.

  


  (** *Event semantics for Clight_core*)
  (* This should be a version of CLC_memsem annotated with memory events. *)
  Program Definition CLC_evsem ge : @EvSem state := {| msem := CLC_memsem ge |}.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.

  Lemma CLC_msem : forall ge, msem (CLC_evsem ge) = CLC_memsem ge.
  Proof. auto. Qed.


  Instance ClightSem ge : Semantics :=
    { semG := G; semC := state; semSem := CLC_evsem ge; the_ge := ge }.

  (* extending Clight_sim to event semantics *)
Inductive ev_star ge: state -> mem -> _ -> state -> mem -> Prop :=
  | ev_star_refl: forall s m,
      ev_star ge s m nil s m
  | ev_star_step: forall s1 m1 ev1 s2 m2 ev2 s3 m3,
      ev_step (CLC_evsem ge) s1 m1 ev1 s2 m2 -> ev_star ge s2 m2 ev2 s3 m3 ->
      ev_star ge s1 m1 (ev1 ++ ev2) s3 m3.

Lemma ev_star_one:
  forall ge s1 m1 ev s2 m2, ev_step (CLC_evsem ge) s1 m1 ev s2 m2 -> ev_star ge s1 m1 ev s2 m2.
Proof.
  intros. rewrite <- (app_nil_r ev). eapply ev_star_step; eauto. apply ev_star_refl.
Qed.

Lemma ev_star_two:
  forall ge s1 m1 ev1 s2 m2 ev2 s3 m3,
  ev_step (CLC_evsem ge) s1 m1 ev1 s2 m2 -> ev_step (CLC_evsem ge) s2 m2 ev2 s3 m3 ->
  ev_star ge s1 m1 (ev1 ++ ev2) s3 m3.
Proof.
  intros. eapply ev_star_step; eauto. apply ev_star_one; auto.
Qed.

Lemma ev_star_trans:
  forall ge {s1 m1 ev1 s2 m2}, ev_star ge s1 m1 ev1 s2 m2 ->
  forall {ev2 s3 m3}, ev_star ge s2 m2 ev2 s3 m3 -> ev_star ge s1 m1 (ev1 ++ ev2) s3 m3.
Proof.
  induction 1; intros; auto.
  rewrite <- app_assoc.
  eapply ev_star_step; eauto.
Qed.


Inductive ev_plus ge: state -> mem -> _ -> state -> mem -> Prop :=
  | ev_plus_left: forall s1 m1 ev1 s2 m2 ev2 s3 m3,
      ev_step (CLC_evsem ge) s1 m1 ev1 s2 m2 -> ev_star ge s2 m2 ev2 s3 m3 ->
      ev_plus ge s1 m1 (ev1 ++ ev2) s3 m3.

Lemma ev_plus_one:
  forall ge s1 m1 ev s2 m2, ev_step (CLC_evsem ge) s1 m1 ev s2 m2 -> ev_plus ge s1 m1 ev s2 m2.
Proof.
  intros. rewrite <- (app_nil_r ev). eapply ev_plus_left; eauto. apply ev_star_refl.
Qed.

Lemma ev_plus_two:
  forall ge s1 m1 ev1 s2 m2 ev2 s3 m3,
  ev_step (CLC_evsem ge) s1 m1 ev1 s2 m2 -> ev_step (CLC_evsem ge) s2 m2 ev2 s3 m3 ->
  ev_plus ge s1 m1 (ev1 ++ ev2) s3 m3.
Proof.
  intros. eapply ev_plus_left; eauto. apply ev_star_one; auto.
Qed.

Lemma ev_plus_star: forall ge s1 m1 ev s2 m2, ev_plus ge s1 m1 ev s2 m2 -> ev_star ge s1 m1 ev s2 m2.
Proof.
  intros. inv H. eapply ev_star_step; eauto.
Qed.

Lemma ev_plus_trans:
  forall ge {s1 m1 ev1 s2 m2}, ev_plus ge s1 m1 ev1 s2 m2 ->
  forall {ev2 s3 m3}, ev_plus ge s2 m2 ev2 s3 m3 -> ev_plus ge s1 m1 (ev1 ++ ev2) s3 m3.
Proof.
  intros.
  inv H.
  rewrite <- app_assoc.
  eapply ev_plus_left. eauto.
  eapply ev_star_trans; eauto.
  apply ev_plus_star. auto.
Qed.

Lemma ev_star_plus_trans:
  forall ge {s1 m1 ev1 s2 m2}, ev_star ge s1 m1 ev1 s2 m2 ->
  forall {ev2 s3 m3}, ev_plus ge s2 m2 ev2 s3 m3 -> ev_plus ge s1 m1 (ev1 ++ ev2) s3 m3.
Proof.
  intros. inv H. auto.
  rewrite <- app_assoc.
  eapply ev_plus_left; eauto.
  eapply ev_star_trans; eauto. apply ev_plus_star; auto.
Qed.

Lemma ev_plus_star_trans:
  forall ge {s1 m1 ev1 s2 m2}, ev_plus ge s1 m1 ev1 s2 m2 ->
  forall {ev2 s3 m3}, ev_star ge s2 m2 ev2 s3 m3 -> ev_plus ge s1 m1 (ev1 ++ ev2) s3 m3.
Proof.
  intros.
  inv H.
  rewrite <- app_assoc.
  eapply ev_plus_left; eauto. eapply ev_star_trans; eauto.
Qed.

  Lemma Clight_new_ev_sim : forall ge c1 m ev c1' m',
    event_semantics.ev_step (@semSem (Clight_newSem ge)) c1 m ev c1' m' ->
    forall c2, match_states c1 (fst (CC'.CC_state_to_CC_core c2)) ->
    exists c2', ev_plus ge c2 m ev c2' m' /\
      match_states c1' (fst (CC'.CC_state_to_CC_core c2')).
  Proof.
    (* based on Clight_sim.Clightnew_Clight_sim_eq_noOrder_SSplusConclusion *)
  Admitted.


End ClightSEM.
