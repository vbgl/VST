(* Clight Safety*)

(**
   Prove that csafety in Clight_new implies safety in Clight. 
*)
Require Import compcert.lib.Integers.
Require Import compcert.lib.Coqlib.
Require Import compcert.common.Values.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import VST.concurrency.common.core_semantics.
Require Import VST.concurrency.common.bounded_maps.
Require Import VST.concurrency.common.threadPool.
Require Import VST.concurrency.common.permissions.
Require Import VST.concurrency.common.HybridMachineSig.
Require Import VST.concurrency.common.ClightSemantincsForMachines.
Require Import VST.concurrency.common.ClightMachine.
Require Import VST.concurrency.juicy.semax_to_juicy_machine.
Require Import VST.veric.Clight_sim.
Require Import VST.msl.eq_dec.
Require Import BinNums.
Require Import List.

Import HybridMachineSig.
Import HybridMachine.
Import HybridCoarseMachine.
Import ListNotations.
Import ThreadPool.
Import event_semantics.

Set Bullet Behavior "Strict Subproofs".

Section Clight_safety_equivalence.
Context (CPROOF : semax_to_juicy_machine.CSL_proof).
Definition prog:= CPROOF.(CSL_prog).
Definition ge:= Clight.globalenv prog.
Definition init_mem:= proj1_sig (init_mem CPROOF).

(*We should be able to construct a Clight.state from the proof... *)
Definition f_main : {f | Genv.find_funct_ptr (Clight.genv_genv ge) (projT1 (spr CPROOF)) = Some f}.
Proof.
  destruct (spr CPROOF) as (b & q & [? Hinit] & s); simpl in *.
  unfold juicy_extspec.j_initial_core in Hinit; simpl core_semantics.initial_core in Hinit.
  destruct (s O tt) as (jm & Hjm & _).
  specialize (Hinit _ Hjm); simpl Genv.find_funct_ptr in Hinit.
  unfold prog, semax_to_juicy_machine.prog in *.
  destruct (Genv.find_funct_ptr _ _); eauto.
  exfalso.
  destruct Hinit as (? & ? & ? & ?); discriminate.
Defined.

(* Clight_new starts a step earlier than Clight, with a sequence of the initial call to main and
   an infinite loop. *)
(* This could be simplified if we made some assumptions about main (e.g., that it has no arguments). *)
Definition initial_Clight_state : Clight.state :=
  let f := proj1_sig f_main in
  Clight.State main_handler (Clight.Scall None (Clight.Etempvar 1%positive (Clight.type_of_fundef f))
             (map (fun x => Clight.Etempvar (fst x) (snd x))
             (Clight_new.params_of_types 2 (Clight_new.params_of_fundef f))))
             (Clight.Kseq (Clight.Sloop Clight.Sskip Clight.Sskip) Clight.Kstop) Clight.empty_env
             (Clight_new.temp_bindings 1 [Vptr (projT1 (spr CPROOF)) Ptrofs.zero]) init_mem.

(*...And we should be able to construct an initial state from the Clight_new and mem.*)
(* See also veric/Clight_sim.v. *)
Fixpoint make_cont k :=
  match k with
  | nil => Clight.Kstop
  | Clight_new.Kseq s :: k' => Clight.Kseq s (make_cont k')
  | Clight_new.Kloop1 s1 s2 :: k' => Clight.Kloop1 s1 s2 (make_cont k')
  | Clight_new.Kloop2 s1 s2 :: k' => Clight.Kloop2 s1 s2 (make_cont k')
  | Clight_new.Kswitch :: k' => Clight.Kswitch (make_cont k')
  | Clight_new.Kcall r f e te :: k' => Clight.Kcall r f e te (make_cont k')
  end.

(* This function assumes that q is an initial state. *)
Definition new2Clight_state (q : Clight_new.corestate) (m : mem) : option Clight.state :=
  match q with
  | Clight_new.State e te (Clight_new.Kseq s :: k) =>
      Some (Clight.State main_handler s (make_cont k) e te m)
(*  | Clight_new.ExtCall f args _ e te k => Some (Clight.Callstate (Ctypes.External f tyargs tyret cc) args (make_cont k) m)*)
(* main shouldn't be an extcall anyway *)
  | _ => None
  end.

(*The two constructions coincide.*)
Lemma initial_Clight_state_correct:
  new2Clight_state
    (initial_corestate CPROOF)
    init_mem = Some initial_Clight_state.
Proof.
  unfold initial_corestate, initial_Clight_state.
  destruct f_main as [f Hf].
  destruct spr as (b & q & [? Hinit] & H); simpl.
  destruct (H O tt) as (jm & Hjm & ?).
  destruct (Hinit _ Hjm) as (? & ? & Hinit' & ?); subst.
  simpl in Hinit', Hf.
  unfold prog, semax_to_juicy_machine.prog in *.
  rewrite Hf in Hinit'; inv Hinit'; auto.
Qed.

Inductive match_ctl : ctl -> ctl -> Prop :=
| match_Krun c c' : match_states c (fst (CC'.CC_state_to_CC_core c')) -> match_ctl (Krun c) (Krun c')
| match_Kblocked c c' : match_states c (fst (CC'.CC_state_to_CC_core c')) -> match_ctl (Kblocked c) (Kblocked c')
| match_Kresume c c' v : match_states c (fst (CC'.CC_state_to_CC_core c')) -> match_ctl (Kresume c v) (Kresume c' v)
| match_Kinit v v' : match_ctl (Kinit v v') (Kinit v v').

(* This should essentially reproduce Clight_sim at the hybrid machine level. *)
Inductive match_st (tp : ThreadPool.t(resources := dryResources)(ThreadPool:= threadPool.OrdinalPool.OrdinalThreadPool(Sem:=Clight_newSem ge)))
  (tp' : ThreadPool.t(resources := dryResources)(ThreadPool:= threadPool.OrdinalPool.OrdinalThreadPool(Sem:=ClightSem ge))) : Prop :=
    MATCH_ST: forall (mtch_cnt: forall {tid},  containsThread tp tid -> containsThread tp' tid)
                (mtch_cnt': forall {tid}, containsThread tp' tid -> containsThread tp tid)
                (mtch_gtc: forall {tid} (Htid:containsThread tp tid)(Htid':containsThread tp' tid),
                    match_ctl (getThreadC Htid) (getThreadC Htid'))
                (mtch_gtr1: forall {tid} (Htid:containsThread tp tid)(Htid':containsThread tp' tid)
                    b ofs,
                    (fst (getThreadR Htid)) !! b ofs = (fst (getThreadR Htid')) !! b ofs)
                (mtch_gtr2: forall {tid} (Htid:containsThread tp tid)(Htid':containsThread tp' tid),
                    snd (getThreadR Htid) = snd (getThreadR Htid'))
                (mtch_locks: forall a, lockRes tp a = lockRes tp' a)
                (mtch_latest: latestThread tp = latestThread tp'),
      match_st tp tp'.

Lemma MTCH_compat: forall js ds m,
    match_st js ds ->
    mem_compatible js m ->
    mem_compatible ds m.
Proof.
  intros ? ? ? MTCH mc.
  inversion MTCH; inv mc; constructor; intros.
  - specialize (compat_th0 _ (mtch_cnt' _ cnt)) as [Hlt ?].
    rewrite mtch_gtr2 with (Htid' := cnt) in *; split; auto.
    intros ??; erewrite <- mtch_gtr1; eauto.
  - rewrite <- mtch_locks in H; eauto.
  - rewrite <- mtch_locks in H; eauto.
Qed.

Lemma MTCH_install_perm:
  forall js ds m m' tid (MATCH : match_st js ds)
    (Hcmpt : mem_compatible js m) (Htid : containsThread js tid) (Htid' : containsThread ds tid)
    (Hperm : install_perm _ _ _ Hcmpt Htid m'),
    install_perm _ _ _ (MTCH_compat _ _ _ MATCH Hcmpt) Htid' m'.
Proof.
  simpl; intros.
  hnf in *; subst.
  apply restrPermMap_ext; intro.
  inv MATCH.
  extensionality ofs.
  rewrite mtch_gtr1 with (Htid' := Htid'); auto.
Qed.

Lemma MTCH_invariant:
  forall js ds (MATCH : match_st js ds) (Hinv : invariant js), invariant ds.
Proof.
  intros; inversion MATCH; inv Hinv; constructor; intros.
  - split.
    + intros ??; erewrite <- !mtch_gtr1; apply no_race_thr0; auto.
    + erewrite <- !mtch_gtr2; apply no_race_thr0; auto.
  - rewrite <- mtch_locks in *; eauto.
  - rewrite <- mtch_locks in *; split.
    + intros ??; erewrite <- mtch_gtr1; eapply no_race0; eauto.
    + erewrite <- mtch_gtr2; eapply no_race0; eauto.
  - specialize (thread_data_lock_coh0 _ (mtch_cnt' _ cnti)) as [].
    split; intros.
    + erewrite <- mtch_gtr2.
      intros ??; erewrite <- mtch_gtr1; apply H.
    + erewrite <- mtch_gtr2.
      rewrite <- mtch_locks in *; eauto.
  - rewrite <- mtch_locks in *.
    specialize (locks_data_lock_coh0 _ _ Hres) as [].
    split; intros.
    + intros ??; erewrite <- mtch_gtr1; apply H.
    + rewrite <- mtch_locks in *; eauto.
  - hnf in *.
    intros; rewrite <- mtch_locks.
    specialize (lockRes_valid0 b ofs).
    destruct (lockRes(ThreadPool := OrdinalPool.OrdinalThreadPool) js (b, ofs)) eqn: Hl; auto.
    intros; rewrite <- mtch_locks; auto.
  Unshelve.
  all: auto.
Qed.

Lemma MTCH_updThread:
  forall tp tp' tid c c' r r' (MATCH : match_st tp tp')
    (Htid : containsThread tp tid) (Htid' : containsThread tp' tid) (Hctl : match_ctl c c')
    (Hr1: forall b ofs, (fst r) !! b ofs = (fst r') !! b ofs) (Hr2: snd r = snd r'),
  match_st (updThread Htid c r) (updThread Htid' c' r').
Proof.
  inversion 1; intros; constructor; auto; intros.
  - destruct (eq_dec tid0 tid).
    + subst; rewrite !gssThreadCode; auto.
    + unshelve erewrite !gsoThreadCode; auto.
  - destruct (eq_dec tid0 tid).
    + subst; rewrite !gssThreadRes; auto.
    + unshelve erewrite !gsoThreadRes; auto.
  - destruct (eq_dec tid0 tid).
    + subst; rewrite !gssThreadRes; auto.
    + unshelve erewrite !gsoThreadRes; auto.
Qed.

Lemma MTCH_updThreadC:
  forall tp tp' tid c c' (MATCH : match_st tp tp')
    (Htid : containsThread tp tid) (Htid' : containsThread tp' tid) (Hctl : match_ctl c c'),
  match_st (updThreadC Htid c) (updThreadC Htid' c').
Proof.
  inversion 1; intros; constructor; auto; intros.
  destruct (eq_dec tid0 tid).
  + subst; rewrite !gssThreadCC; auto.
  + unshelve erewrite <- !gsoThreadCC; auto.
Qed.

Lemma MTCH_updLockSet:
  forall tp tp' a l (MATCH : match_st tp tp'),
  match_st (updLockSet tp a l) (updLockSet tp' a l).
Proof.
  inversion 1; intros; constructor; auto; intros.
  destruct (eq_dec a0 a).
  - subst; rewrite !gssLockRes; auto.
  - rewrite !gsoLockRes; auto.
Qed.

Lemma MTCH_remLockSet:
  forall tp tp' a (MATCH : match_st tp tp'),
  match_st (remLockSet tp a) (remLockSet tp' a).
Proof.
  inversion 1; intros; constructor; auto; intros.
  destruct (eq_dec a0 a).
  - subst; rewrite !gsslockResRemLock; auto.
  - rewrite !gsolockResRemLock; auto.
Qed.

Lemma MTCH_addThread:
  forall tp tp' vf arg r (MATCH : match_st tp tp'),
  match_st (addThread tp vf arg r) (addThread tp' vf arg r).
Proof.
  inversion 1; intros; constructor; auto; intros.
  - apply cntAdd' in H as [[]|].
    + apply cntAdd; auto.
    + subst; rewrite mtch_latest.
      apply cntAddLatest.
  - apply cntAdd' in H as [[]|].
    + apply cntAdd; auto.
    + subst; rewrite <- mtch_latest.
      apply cntAddLatest.
  - destruct (cntAdd' _ _ _ Htid) as [[]|], (cntAdd' _ _ _ Htid') as [[]|]; try congruence.
    + unshelve erewrite !gsoAddCode; eauto.
    + subst; rewrite !gssAddCode; auto.
      constructor.
  - destruct (cntAdd' _ _ _ Htid) as [[]|], (cntAdd' _ _ _ Htid') as [[]|]; try congruence.
    + unshelve erewrite !gsoAddRes; eauto.
    + subst; rewrite !gssAddRes; auto.
  - destruct (cntAdd' _ _ _ Htid) as [[]|], (cntAdd' _ _ _ Htid') as [[]|]; try congruence.
    + unshelve erewrite !gsoAddRes; eauto.
    + subst; rewrite !gssAddRes; auto.
  - simpl in *.
    unfold OrdinalPool.latestThread, OrdinalPool.addThread in *; simpl.
    congruence.
Qed.

Existing Instance scheduler.
Existing Instance DilMem.

Lemma updThread_twice : forall {res sem} (tp : @OrdinalPool.t res sem) i
  (cnti : containsThread(ThreadPool := OrdinalPool.OrdinalThreadPool) tp i) c c' r r'
  (cnti' : containsThread (updThread cnti c r) i),
  updThread cnti' c' r' = updThread cnti c' r'.
Proof.
  intros; apply OrdinalPool.updThread_twice.
Qed.

Lemma mem_ext: forall m1 m2,
  Mem.mem_contents m1 = Mem.mem_contents m2 ->
  Mem.mem_access m1 = Mem.mem_access m2 ->
  Mem.nextblock m1 = Mem.nextblock m2 ->
  m1 = m2.
Proof.
  destruct m1, m2; simpl; intros; subst.
  f_equal; apply Axioms.proof_irr.
Qed.

Lemma restrPermMap_twice: forall p1 p2 m Hlt1 Hlt2 Hlt',
  @restrPermMap p2 (@restrPermMap p1 m Hlt1) Hlt2 = @restrPermMap p2 m Hlt'.
Proof.
  intros; apply mem_ext; try reflexivity.
  simpl.
  f_equal.
  + repeat (apply Axioms.functional_extensionality; intro).
    destruct x0; auto.
  + remember (snd (Mem.mem_access m)) as t.
    unfold PTree.map.
    remember 1%positive as n.
    clear.
    revert n; induction t; auto; intro; simpl; f_equal; eauto.
    destruct o; reflexivity.
Qed.

Lemma restrPermMap_compat: forall {Sem} (tp : t(ThreadPool:= OrdinalPool.OrdinalThreadPool(Sem:=Sem)))
  m p Hlt, mem_compatible tp (@restrPermMap p m Hlt) -> mem_compatible tp m.
Proof.
  destruct 1; constructor.
  + split; repeat intro; eapply juicy_mem.perm_order''_trans; try apply compat_th0;
      rewrite getMax_restr; apply po_refl.
  + split; repeat intro; eapply juicy_mem.perm_order''_trans; try eapply compat_lp0; eauto;
      rewrite getMax_restr; apply po_refl.
  + intros; rewrite <- restrPermMap_valid; eauto.
Qed.

Lemma restrPerm_sub_map: forall m p Hlt,
  sub_map (snd (getMaxPerm (@restrPermMap p m Hlt))) (snd (getMaxPerm m)).
Proof.
  intros; simpl; apply sub_map_and_shape.
  { unfold PTree.map.
    remember (snd (Mem.mem_access m)) as t; remember 1%positive as i; clear.
    revert i; unfold same_shape; induction t; simpl; auto; intros.
    repeat split; auto.
    destruct o; simpl; auto. }
  intros ??.
  rewrite !PTree.gmap1, PTree.gmap.
  intro H; destruct ((snd (Mem.mem_access m)) ! _); inv H.
  simpl; do 2 eexists; eauto.
  intro; auto.
Qed.

Lemma csafe_restr: forall {Sem} n st m p' Hlt
  (Hext: forall c m m' e, at_external (msem semSem) c m = Some e -> at_external (msem semSem) c m' = Some e),
  @csafe _ Sem OrdinalPool.OrdinalThreadPool DryHybridMachineSig st (@restrPermMap p' m Hlt) n ->
  @csafe _ Sem OrdinalPool.OrdinalThreadPool DryHybridMachineSig st m n.
Proof.
  induction n; intros; [constructor|].
  destruct st as ((U, tr), tp).
  inv H; [constructor; auto | inv Hstep; simpl in *; try inv Htstep; try (apply schedSkip_id in HschedS; subst);
      try discriminate | inv Hstep; simpl in *; try inv Htstep; try match goal with H : U = schedSkip U |- _ =>
      symmetry in H; apply schedSkip_id in H; subst end; try discriminate];
      pose proof (restrPermMap_compat _ _ _ _ Hcmpt) as Hcmpt'.
  - hnf in Hperm; subst.
    erewrite restrPermMap_twice in *.
    eapply CoreSafe; eauto.
    hnf; simpl.
    change U with (yield U) at 2.
    change m'0 with (diluteMem m'0) at 2.
    rewrite <- H4.
    eapply start_step; eauto.
    econstructor; eauto.
    instantiate (2 := Hcmpt').
    hnf; eauto.
  - hnf in Hperm; subst.
    erewrite restrPermMap_twice in *.
    eapply CoreSafe, IHn; eauto.
    hnf; simpl.
    change U with (yield U) at 2.
    change m with (diluteMem m) at 2.
    rewrite <- H4.
    eapply resume_step; eauto.
    econstructor; eauto.
    instantiate (2 := Hcmpt').
    hnf; eauto.
  - erewrite restrPermMap_twice in *.
    eapply CoreSafe; eauto.
    hnf; simpl.
    change U with (yield U) at 2.
    change m'0 with (diluteMem m'0) at 2.
    rewrite <- H5.
    eapply thread_step; eauto.
    instantiate (1 := Hcmpt').
    econstructor; eauto.
  - hnf in Hperm; subst.
    erewrite restrPermMap_twice in *.
    eapply AngelSafe; [|intro; eapply IHn; eauto].
    hnf; simpl.
    rewrite <- H4.
    eapply suspend_step; eauto.
    econstructor; eauto.
    instantiate (2 := Hcmpt').
    hnf; eauto.
  - assert (permMapLt (setPermBlock (Some Writable) b (Ptrofs.intval ofs)
      (snd (getThreadR(ThreadPool := OrdinalPool.OrdinalThreadPool) Htid)) LKSIZE_nat)
      (getMaxPerm m)) as H.
    { repeat intro; eapply juicy_mem.perm_order''_trans, Hlt'; rewrite getMax_restr; apply po_refl. }
    erewrite restrPermMap_twice in *.
    instantiate (1 := H) in Hstore.
    eapply AngelSafe; eauto.
    hnf; simpl.
    rewrite <- H5.
    eapply sync_step; auto.
    instantiate (1 := Hcmpt').
    pose proof (restrPerm_sub_map _ _ Hlt).
    eapply step_acquire; eauto.
    destruct Hbounded; split; eapply sub_map_trans; eauto.
  - assert (permMapLt (setPermBlock (Some Writable) b (Ptrofs.intval ofs)
      (snd (getThreadR(ThreadPool := OrdinalPool.OrdinalThreadPool) Htid)) LKSIZE_nat)
      (getMaxPerm m)) as H.
    { repeat intro; eapply juicy_mem.perm_order''_trans, Hlt'; rewrite getMax_restr; apply po_refl. }
    erewrite restrPermMap_twice in *.
    instantiate (1 := H) in Hstore.
    eapply AngelSafe; eauto.
    hnf; simpl.
    rewrite <- H5.
    eapply sync_step; auto.
    instantiate (1 := Hcmpt').
    pose proof (restrPerm_sub_map _ _ Hlt).
    destruct Hbounded, HboundedLP as (? & ? & ? & ?).
    eapply step_release; eauto; repeat split; auto; eapply sub_map_trans; eauto.
  - eapply AngelSafe; [|intro; eapply IHn; eauto].
    hnf; simpl.
    rewrite <- H5.
    eapply sync_step; auto.
    instantiate (1 := Hcmpt').
    pose proof (restrPerm_sub_map _ _ Hlt).
    destruct Hbounded, Hbounded_new.
    eapply step_create; eauto; simpl; auto; split; eapply sub_map_trans; eauto.
  - erewrite restrPermMap_twice in *.
    eapply AngelSafe; eauto.
    hnf; simpl.
    rewrite <- H5.
    eapply sync_step; auto.
    instantiate (1 := Hcmpt').
    eapply step_mklock; eauto.
  - erewrite restrPermMap_twice in *.
    eapply AngelSafe; [|intro; eapply IHn; eauto].
    hnf; simpl.
    rewrite <- H5.
    eapply sync_step; auto.
    instantiate (1 := Hcmpt').
    eapply step_freelock; eauto; simpl; auto.
  - erewrite restrPermMap_twice in *.
    eapply AngelSafe; [|intro; eapply IHn; eauto].
    hnf; simpl.
    rewrite <- H5.
    eapply sync_step; auto.
    instantiate (1 := Hcmpt').
    eapply step_acqfail; eauto.
  - eapply AngelSafe; [|intro; eapply IHn; eauto].
    hnf; simpl.
    subst; rewrite <- H4.
    eapply halted_step; eauto.
  - eapply AngelSafe; [|intro; eapply IHn; eauto].
    hnf; simpl.
    subst; rewrite <- H4.
    eapply schedfail; eauto.
Qed.

Lemma restr_Cur: forall p m Hlt, p = getCurPerm m -> @restrPermMap p m Hlt = m.
Proof.
  intros; subst; apply mem_ext; auto; simpl.
  pose proof Clight_bounds.Mem_canonical_useful m.
  destruct (Mem.mem_access m) eqn: Hm; simpl in *; f_equal.
  - extensionality ofs; extensionality k; rewrite H.
    destruct k; auto.
  - apply sync_preds.PTree_map_self; intros.
    extensionality ofs; extensionality k.
    destruct k; auto.
    rewrite getCurPerm_correct; unfold permission_at.
    rewrite Hm; simpl.
    unfold PMap.get; simpl.
    rewrite H0; auto.
Qed.

Corollary csafe_restr': forall n st m p' Hlt,
  csafe(ThreadPool:= OrdinalPool.OrdinalThreadPool(Sem:=ClightSem ge))
    (machineSig:= HybridMachine.DryHybridMachine.DryHybridMachineSig) st m n ->
  csafe(ThreadPool:= OrdinalPool.OrdinalThreadPool(Sem:=ClightSem ge))
    (machineSig:= HybridMachine.DryHybridMachine.DryHybridMachineSig) st (@restrPermMap p' m Hlt) n.
Proof.
  intros.
  unshelve eapply csafe_restr; [.. | unshelve erewrite restrPermMap_twice, restr_Cur; auto].
  - intros ??; rewrite getMax_restr.
    apply getCur_Max.
  - simpl.
    destruct c; auto.
  - intros ??; apply getCur_Max.
Qed.

Lemma invariant_updThreadC: forall (tp : t(ThreadPool:= OrdinalPool.OrdinalThreadPool(Sem:=ClightSem ge)))
  tid c (cnti : containsThread tp tid),
  invariant tp -> invariant (updThreadC cnti c).
Proof.
  destruct 1; constructor; auto.
Qed.

Lemma CoreSafe_star: forall n U tr tp m tid (c : @semC (ClightSem ge)) c' tp' m' ev
  (HschedN: schedPeek U = Some tid)
  (Htid: containsThread tp tid)
  (Hm: fst (getThreadR(resources:=dryResources) Htid) = getCurPerm m)
  (Hcmpt: mem_compatible tp m)
  (Hinv: invariant tp)
  (Hcode: getThreadC Htid = Krun c)
  (Hcoresteps: ev_star ge c m ev c' m')
  (Htp': tp' = updThread Htid (Krun c') (getCurPerm m', snd (getThreadR Htid)))
  (Hsafe: csafe(ThreadPool:= OrdinalPool.OrdinalThreadPool(Sem:=ClightSem ge))
    (machineSig:= HybridMachine.DryHybridMachine.DryHybridMachineSig)
    (yield U, seq.cat tr (map (fun mev => Events.internal tid mev) ev), tp') (diluteMem m') n),
  csafe(ThreadPool:= OrdinalPool.OrdinalThreadPool(Sem:=ClightSem ge))
    (machineSig:= HybridMachine.DryHybridMachine.DryHybridMachineSig)
    (U, tr, tp) m n.
Proof.
  intros.
  revert dependent tp'.
  revert dependent tp.
  revert n tr.
  induction Hcoresteps; intros.
  - subst.
    rewrite app_nil_r in Hsafe.
    rewrite <- Hm in Hsafe.
    destruct (getThreadR Htid) eqn: Hget; simpl in *.
    rewrite <- Hcode, <- Hget, OrdinalPool.updThread_same in Hsafe; auto.
  - rewrite map_app, app_assoc in Hsafe.
    eapply IHHcoresteps in Hsafe.
    + eapply csafe_reduce; [eapply CoreSafe; eauto | auto].
      hnf; simpl.
      change U with (yield U) at 2.
      change m2 with (diluteMem m2) at 2.
      eapply thread_step with (Hcmpt0 := Hcmpt); auto; simpl.
      econstructor; try apply H; eauto.
      apply restr_Cur; auto.
    + rewrite gssThreadRes; auto.
    + admit. (* need to know that step preserved mem_compatible *)
    + admit. (* ditto invariant *)
    + apply gssThreadCode.
    + rewrite updThread_twice, gssThreadRes; auto.
  Unshelve.
  apply cntUpdate; auto.
Admitted.

Lemma CoreSafe_plus : forall n U tr tp m tid (c : @semC (ClightSem ge)) c' tp' m' ev m1
  (HschedN: schedPeek U = Some tid)
  (Htid: containsThread tp tid)
  (Hcmpt: mem_compatible tp m)
  (Hrestrict_pmap: restrPermMap (proj1 (compat_th _ _ Hcmpt Htid)) = m1)
  (Hinv: invariant tp)
  (Hcode: getThreadC Htid = Krun c)
  (Hcoresteps: ev_plus ge c m1 ev c' m')
  (Htp': tp' = updThread Htid (Krun c') (getCurPerm m', snd (getThreadR Htid)))
  (Hsafe: csafe(ThreadPool:= OrdinalPool.OrdinalThreadPool(Sem:=ClightSem ge))
    (machineSig:= HybridMachine.DryHybridMachine.DryHybridMachineSig)
    (yield U, seq.cat tr (map (fun mev => Events.internal tid mev) ev), tp') (diluteMem m') n),
  csafe(ThreadPool:= OrdinalPool.OrdinalThreadPool(Sem:=ClightSem ge))
    (machineSig:= HybridMachine.DryHybridMachine.DryHybridMachineSig)
    (U, tr, tp) m (S n).
Proof.
  intros.
  inv Hcoresteps.
  rewrite map_app, app_assoc in Hsafe.
  eapply CoreSafe_star in Hsafe; try apply H0.
  - eapply CoreSafe; eauto.
    hnf; simpl.
    change U with (yield U) at 2.
    change m2 with (diluteMem m2) at 2.
    eapply thread_step; auto.
    econstructor; eauto.
    simpl; eauto.
  - auto.
  - rewrite gssThreadRes; auto.
  - admit.
  - admit.
  - apply gssThreadCode.
  - rewrite updThread_twice, gssThreadRes; auto.
  Unshelve.
  apply cntUpdate; auto.
Admitted.

Opaque updThread updThreadC containsThread getThreadC getThreadR lockRes.

Lemma computeMap_ext: forall pmap pmap' dmap, (forall b ofs, pmap !! b ofs = pmap' !! b ofs) ->
  forall b ofs, (computeMap pmap dmap) !! b ofs = (computeMap pmap' dmap) !! b ofs.
Proof.
  intros.
  destruct (dmap ! b) eqn: Hb; [|rewrite !computeMap_3; auto].
  destruct (o ofs) eqn: Hofs; [erewrite !computeMap_1 by eauto | erewrite !computeMap_2 by eauto]; auto.
Qed.

Lemma type_of_fundef_fun: forall f, exists targs tres cc,
  Clight.type_of_fundef f = Ctypes.Tfunction targs tres cc.
Proof.
  destruct f; simpl; eauto.
  unfold Clight.type_of_function; eauto.
Qed.

(* spawn handler *)
Parameter b_wrapper: block.
Parameter f_wrapper: Clight.function.
Axiom lookup_wrapper: Genv.find_funct_ptr (Clight.genv_genv ge) b_wrapper = Some (Ctypes.Internal f_wrapper).
Axiom wrapper_args: forall l, In l (AST.regs_of_rpairs (Clight.loc_arguments' (map Ctypes.typ_of_type (map snd (Clight.fn_params f_wrapper))))) ->
        match l with Locations.R _ => True | Locations.S _ _ _ => False end.

Lemma Clight_new_Clight_safety_gen:
  forall n sch tr tp m tp' (Hglobals : Smallstep.globals_not_fresh (Clight.genv_genv ge) m),
  csafe
    (Sem := Clight_newSem ge)
    (machineSig:= HybridMachine.DryHybridMachine.DryHybridMachineSig)
    (sch, tr, tp) m (n * 2) ->
  match_st tp tp' ->
  csafe
    (Sem := ClightSem ge)
    (ThreadPool:= OrdinalPool.OrdinalThreadPool(Sem:=ClightSem ge))
    (machineSig:= HybridMachine.DryHybridMachine.DryHybridMachineSig)
    (sch, tr, tp') m n.
Proof.
  induction n; intros; [constructor|].
  inv H; simpl in *; [constructor; auto |
    inv Hstep; simpl in *; try (apply schedSkip_id in HschedS; subst); try discriminate |
    inv Hstep; simpl in *; try match goal with H : sch = schedSkip sch |- _ =>
      symmetry in H; apply schedSkip_id in H; subst end; try discriminate].
  - inv Htstep.
    inversion H0.
    pose proof (mtch_gtc _ ctn (mtch_cnt _ ctn)) as Hc; rewrite Hcode in Hc; inv Hc.
    destruct Hinitial as [Hinit ?]; subst.
    unfold Clight_new.cl_initial_core in Hinit.
    destruct vf; try discriminate.
    destruct (Ptrofs.eq_dec _ _); try discriminate.
    destruct (Genv.find_funct_ptr _ b) eqn: Hb; inv Hinit.
    destruct (Mem.alloc _ _ _) eqn: Halloc.
    eapply CoreSafe.
    { hnf; simpl.
      rewrite <- H5.
      change sch with (yield sch) at 2.
      eapply start_step; eauto; econstructor; eauto.
      { eapply MTCH_install_perm, Hperm. }
      { split.
        destruct (type_of_fundef_fun f) as (targs & tres & cc & ?).
        assert (cc = AST.cc_default) by admit; subst.
        hnf in Hperm; subst.
        econstructor; eauto.
        - admit. (* Clight_new's initial_core doesn't currently require mem_wd *)
        - repeat constructor.
          admit. (* check that arg is valid if it's a pointer *)
        - admit. (* right number/type of args *)
        - admit. (* right number/type of args *)
        - apply lookup_wrapper.
        - apply wrapper_args.
        - auto. }
      { eapply MTCH_invariant; eauto. } }
    simpl.
    destruct n; [constructor|].
    (* Clight_new needs to take another step to enter the call; then, if it's an internal
       function, Clight needs to take another step to match. *)
    inv Hsafe; simpl in *.
    { unfold halted_machine in H1; simpl in H1.
      rewrite HschedN in H1; discriminate. }
    inv Hstep; simpl in *; rewrite HschedN in HschedN0; inv HschedN0;
      try (inv Htstep; rewrite gssThreadCode in Hcode0; inv Hcode0);
      try (apply schedSkip_id in HschedS; subst); try discriminate.
    apply app_inv_head in H9; subst.
    pose proof (ev_step_ax1 _ _ _ _ _ _ Hcorestep) as Hstep; inv Hstep.
    { (* internal step *)
      inv H11; [|inv H1].
      inv H6; simpl in *.
      rewrite Hb in H16; inv H16.
      assert (vargs = [arg]); subst.
      { admit. (* cl_initial_core doesn't enforce that we provide the right number of arguments *) }
      eapply CoreSafe with (m'0 := m'1), csafe_reduce; [| eapply IHn; eauto | auto].
      - hnf; simpl.
        rewrite <- H5.
        change sch with (yield sch) at 3.
        change m'1 with (diluteMem m'1) at 2.
        eapply thread_step; eauto; econstructor; eauto.
        { admit. }
        { apply (gssThreadCode (mtch_cnt _ ctn)). }
        edestruct (ev_step_ax2 (@semSem (ClightSem ge))) as [ev' Hstep];
          [|assert (ev' = ev); [|subst; apply Hstep]].
        econstructor; auto.
        hnf; simpl.
        instantiate (1 := Clight.State _ _ _ _ _ _).
        apply Clight.step_internal_function.
        apply list_norepet_app in H18 as (? & ? & ?).
        constructor; eauto.
        admit.
        { admit. }
      - admit. (* globals_not_fresh *)
      - rewrite !updThread_twice.
        apply MTCH_updThread; auto.
        + constructor; constructor; [simpl; auto|].
          admit.
        + rewrite !gssThreadRes; simpl.
          erewrite mtch_gtr2; eauto. }
    { (* external call *)
      inv H14; [|inv H1].
      inv H6; simpl in *.
      rewrite Hb in H16; inv H16.
      assert (vargs = [arg]); subst.
      { admit. (* cl_initial_core doesn't enforce that we provide the right number of arguments *) }
      assert (ev = nil) by admit; subst.
      rewrite app_nil_r in Hsafe0.
      eapply IHn; eauto.
      { admit. (* globals_not_fresh *) }
      { eapply csafe_restr, Hsafe0.
        destruct c; auto. }
      { rewrite updThread_twice.
        apply MTCH_updThread; auto.
        + constructor.
(*          apply match_states_ext.*)
          admit. (* Clight_new puts the arguments in the temp environment in the wrapper,
                    so that they can be passed to the function, but this is fairly arbitrary. *)
        + intros; simpl.
          rewrite !getCurPerm_correct, restrPermMap_Cur.
          rewrite gssThreadRes; simpl.
          apply getCurPerm_correct.
        + simpl.
          rewrite gssThreadRes; simpl.
          erewrite mtch_gtr2; eauto. } }
    { inv Hstep; simpl in *; rewrite HschedN in HschedN0; inv HschedN0;
        try (inv Htstep; rewrite gssThreadCode in Hcode0; inv Hcode0);
        try match goal with H : sch = schedSkip sch |- _ =>
        symmetry in H; apply schedSkip_id in H; subst end; try discriminate; try contradiction.
      inv Hhalted; contradiction. }
  - inv Htstep.
    inversion H0.
    pose proof (mtch_gtc _ ctn (mtch_cnt _ ctn)) as Hc; rewrite Hcode in Hc; inv Hc.
    simpl in *.
    destruct c; inv Hat_external; inv H1.
    destruct c'0; inv H11.
    eapply CoreSafe.
    { hnf; simpl.
      rewrite <- H5.
      change sch with (yield sch) at 2.
      eapply resume_step; eauto; econstructor; eauto; simpl; eauto.
      - eapply MTCH_install_perm, Hperm.
      - eapply MTCH_invariant; eauto. }
    (* In resume, Clight takes another step to process the Returnstate. *)
    destruct n; [constructor|].
    pose proof cntUpdateC(Sem := ClightSem ge) (Krun (Clight.Returnstate Vundef (CC.Kcall lid f ve te k') m))
      (mtch_cnt tid ctn) (mtch_cnt tid ctn) as Htid'.
    eapply CoreSafe.
    { hnf; simpl.
      rewrite <- H5.
      change sch with (yield sch) at 2.
      eapply thread_step with (Htid0 := Htid'); eauto; econstructor; eauto.
      - eapply invariant_updThreadC, MTCH_invariant; eauto.
      - rewrite gssThreadCC; auto.
      - edestruct (ev_step_ax2 (CLC_evsem ge)) as [ev Hstep];
          [|assert (ev = nil); [|subst; apply Hstep]].
        econstructor; auto.
        hnf; simpl.
        instantiate (2 := Clight.State _ _ _ _ _ _).
        apply Clight.step_returnstate.
        { admit. } }
    simpl.
    rewrite app_nil_r.
    apply csafe_restr'.
    eapply (csafe_reduce(ThreadPool := OrdinalPool.OrdinalThreadPool));
      [eapply IHn; [auto | eapply (csafe_reduce(ThreadPool := OrdinalPool.OrdinalThreadPool)); eauto|] | auto].
    constructor; auto; intros.
    + destruct (eq_dec tid0 tid).
      * subst; rewrite gssThreadCode, gssThreadCC.
        constructor.
        destruct lid; inv Hafter_external; constructor; auto.
      * unshelve erewrite gsoThreadCode, <- !gsoThreadCC; auto.
    + destruct (eq_dec tid0 tid).
      * subst; rewrite gssThreadRes.
        unshelve erewrite gThreadCR; auto; simpl.
        rewrite getCurPerm_correct, restrPermMap_Cur.
        unshelve erewrite gThreadCR; auto.
      * rewrite (gThreadCR ctn (cntUpdateC' _ _ Htid0)).
        rewrite (gsoThreadRes Htid' (cntUpdate' _ _ _ Htid'0)); auto.
        unshelve erewrite gThreadCR; auto.
    + destruct (eq_dec tid0 tid).
      * subst; rewrite gssThreadRes.
        unshelve erewrite gThreadCR; auto; simpl.
        unshelve erewrite gThreadCR; auto.
      * rewrite (gThreadCR ctn (cntUpdateC' _ _ Htid0)).
        rewrite (gsoThreadRes Htid' (cntUpdate' _ _ _ Htid'0)); auto.
        unshelve erewrite gThreadCR; auto.
  - inv Htstep.
    inversion H0.
    pose proof (mtch_gtc _ Htid (mtch_cnt _ Htid)) as Hc; rewrite Hcode in Hc; inv Hc.
    eapply Clight_new_ev_sim in Hcorestep as (c2' & Hstep & Hmatch); eauto.
    eapply CoreSafe_plus with (Hcmpt := MTCH_compat _ _ _ H0 Hcmpt); try apply Hstep; eauto.
    + apply restrPermMap_ext.
      intro; extensionality ofs; auto.
    + eapply MTCH_invariant; eauto.
    + rewrite <- H6 in Hsafe.
      eapply IHn.
      { admit. (* globals_not_fresh *) }
      { eapply (csafe_reduce(ThreadPool := OrdinalPool.OrdinalThreadPool)); eauto. }
      apply MTCH_updThread; auto.
      * constructor; auto.
      * erewrite <- mtch_gtr2; eauto.
  - inv Htstep.
    inversion H0.
    pose proof (mtch_gtc _ ctn (mtch_cnt _ ctn)) as Hc; rewrite Hcode in Hc; inv Hc.
    simpl in *.
    destruct c; inv Hat_external; inv H2.
    destruct c'; inv H10.
    eapply AngelSafe.
    { hnf; simpl.
      rewrite app_nil_r.
      eapply suspend_step; eauto; econstructor; eauto; simpl; eauto.
      - eapply MTCH_install_perm, Hperm.
      - eapply MTCH_invariant; eauto. }
    { rewrite app_nil_r; rewrite <- H5 in Hsafe.
      intro; eapply IHn; auto.
      { eapply (csafe_reduce(ThreadPool := OrdinalPool.OrdinalThreadPool)); eauto. }
      apply MTCH_updThreadC; auto.
      constructor; constructor; auto. }
  - inv Htstep; inversion H0; pose proof (mtch_gtc _ Htid (mtch_cnt _ Htid)) as Hc;
      rewrite Hcode in Hc; inv Hc; destruct c; inv Hat_external; destruct c'; inv H2.
    + eapply AngelSafe.
      { eapply sync_step with (Hcmpt0 := MTCH_compat _ _ _ H0 Hcmpt); eauto.
        eapply step_acquire; simpl; eauto; simpl; eauto.
        * eapply MTCH_invariant; eauto.
        * erewrite restrPermMap_irr; eauto.
        * erewrite restrPermMap_irr; eauto.
        * erewrite restrPermMap_irr; eauto.
          erewrite mtch_gtr2; eauto.
        * rewrite <- mtch_locks; eauto.
        * clear - Hangel1 mtch_gtr1.
          repeat intro.
          erewrite <- mtch_gtr1, <- computeMap_ext by eauto; apply Hangel1.
        * erewrite <- mtch_gtr2; apply Hangel2. }
      { rewrite <- H6 in Hsafe.
        intro; eapply IHn.
        { admit. (* globals_not_fresh *) }
        { eapply (csafe_reduce(ThreadPool := OrdinalPool.OrdinalThreadPool)); eauto. }
        apply MTCH_updLockSet, MTCH_updThread; auto.
        - constructor; constructor; auto.
        - apply computeMap_ext; auto.
        - subst newThreadPerm; intros; simpl.
          erewrite mtch_gtr2; eauto. }
    + eapply AngelSafe.
      { eapply sync_step with (Hcmpt0 := MTCH_compat _ _ _ H0 Hcmpt); eauto.
        eapply step_release; simpl; eauto; simpl; eauto.
        * eapply MTCH_invariant; eauto.
        * erewrite restrPermMap_irr; eauto.
        * erewrite restrPermMap_irr; eauto.
        * erewrite restrPermMap_irr; eauto.
          erewrite mtch_gtr2; eauto.
        * rewrite <- mtch_locks; eauto.
        * clear - Hangel1 mtch_gtr1.
          repeat intro.
          specialize (Hangel1 b ofs); simpl in *.
          erewrite <- mtch_gtr1, <- computeMap_ext; eauto.
        * erewrite <- mtch_gtr2; apply Hangel2. }
      { rewrite <- H6 in Hsafe.
        intro; eapply IHn.
        { admit. (* globals_not_fresh *) }
        SearchAbout Smallstep.globals_not_fresh.
        { eapply (csafe_reduce(ThreadPool := OrdinalPool.OrdinalThreadPool)); eauto. }
        apply MTCH_updLockSet, MTCH_updThread; auto.
        - constructor; constructor; auto.
        - apply computeMap_ext; auto.
        - subst newThreadPerm; intros; simpl.
          erewrite mtch_gtr2; eauto. }
    + eapply AngelSafe.
      { eapply sync_step with (Hcmpt0 := MTCH_compat _ _ _ H0 Hcmpt); eauto.
        eapply step_create with (virtue3 := virtue1)(virtue4 := virtue2); simpl; eauto; simpl; eauto.
        * eapply MTCH_invariant; eauto.
        * subst newThreadPerm threadPerm'; intros ??; simpl in *.
          specialize (Hangel1 b0 ofs0).
          erewrite <- mtch_gtr1, <- (computeMap_ext _ _ (fst virtue1)) by eauto; apply Hangel1.
        * erewrite <- mtch_gtr2; apply Hangel2. }
      { rewrite <- H6 in Hsafe.
        intro; eapply IHn; auto.
        { eapply (csafe_trace(ThreadPool := OrdinalPool.OrdinalThreadPool)),
            (csafe_reduce(ThreadPool := OrdinalPool.OrdinalThreadPool)); eauto. }
        apply MTCH_addThread; auto.
        apply MTCH_updThread; auto.
        - constructor; constructor; auto.
        - apply computeMap_ext; auto.
        - subst threadPerm'; intros; simpl.
          erewrite mtch_gtr2; eauto. }
    + eapply AngelSafe.
      { eapply sync_step with (Hcmpt0 := MTCH_compat _ _ _ H0 Hcmpt); eauto.
        eapply step_mklock with (pmap_tid'0 := (_, _)); simpl; eauto; simpl; eauto.
        * eapply MTCH_invariant; eauto.
        * erewrite <- restrPermMap_ext; eauto.
          intro; extensionality ofs0; auto.
        * erewrite <- restrPermMap_ext; eauto.
          intro; extensionality ofs0; auto.
        * rewrite <- mtch_locks; auto. }
      { rewrite <- H6 in Hsafe.
        intro; eapply IHn.
        { admit. (* globals_not_fresh *) }
        { eapply (csafe_reduce(ThreadPool := OrdinalPool.OrdinalThreadPool)); eauto. }
        apply MTCH_updLockSet, MTCH_updThread; auto.
        * constructor; constructor; auto.
        * intros; simpl.
          setoid_rewrite <- Hdata_perm.
          rewrite !addressFiniteMap.setPermBlock_lookup.
          destruct (adr_range_dec _ _ _); auto.
        * simpl.
          setoid_rewrite <- Hlock_perm.
          erewrite <- mtch_gtr2; eauto. }
    + eapply AngelSafe.
      { eapply sync_step with (Hcmpt0 := MTCH_compat _ _ _ H0 Hcmpt); eauto.
        eapply step_freelock with (pmap_tid'0 := (_, _)); simpl; eauto; simpl; eauto.
        * eapply MTCH_invariant; eauto.
        * rewrite <- mtch_locks; auto.
        * erewrite restrPermMap_irr; eauto. }
      { rewrite <- H6 in Hsafe.
        intro; eapply IHn; auto.
        { eapply (csafe_reduce(ThreadPool := OrdinalPool.OrdinalThreadPool)); eauto. }
        apply MTCH_remLockSet, MTCH_updThread; auto.
        * constructor; constructor; auto.
        * intros; simpl.
          setoid_rewrite <- Hdata_perm.
          destruct (adr_range_dec (b, Ptrofs.intval ofs) LKSIZE (b0, ofs0)).
          -- destruct a; subst.
             rewrite !setPermBlock_var_same by (unfold LKSIZE_nat; rewrite Z2Nat.id; lkomega); auto.
          -- destruct (eq_dec b b0); [|rewrite !setPermBlock_var_other_2; auto].
             subst; assert (~(Ptrofs.intval ofs <= ofs0 < Ptrofs.intval ofs + LKSIZE)).
             { intro; contradiction n0; split; auto. }
             rewrite !setPermBlock_var_other_1; auto; unfold LKSIZE_nat; rewrite Z2Nat.id; lkomega.
        * simpl.
          setoid_rewrite <- Hlock_perm.
          erewrite <- mtch_gtr2; eauto. }
    + eapply AngelSafe.
      { eapply sync_step with (Hcmpt0 := MTCH_compat _ _ _ H0 Hcmpt); eauto.
        eapply step_acqfail; simpl; eauto; simpl; eauto.
        * eapply MTCH_invariant; eauto.
        * erewrite restrPermMap_irr; eauto.
        * erewrite restrPermMap_irr; eauto. }
      { rewrite <- H6 in Hsafe.
        intro; eapply IHn; eauto.
        eapply (csafe_reduce(ThreadPool := OrdinalPool.OrdinalThreadPool)); eauto. }
  - inv Hhalted; contradiction.
  - subst; eapply AngelSafe.
    { simpl; rewrite <- H5.
      eapply schedfail; eauto; simpl.
      - inv H0.
        intro; contradiction Htid; apply mtch_cnt'; auto.
      - eapply MTCH_invariant; eauto.
      - eapply MTCH_compat; eauto. }
    { intro; eapply IHn; eauto.
      eapply (csafe_reduce(ThreadPool := OrdinalPool.OrdinalThreadPool)); eauto. }
Admitted.

Transparent getThreadC.

Lemma Clight_new_Clight_safety:
  (forall sch n,
    csafe
      (Sem := Clight_newSem ge)
      (ThreadPool:= threadPool.OrdinalPool.OrdinalThreadPool(Sem:=Clight_newSem ge))
      (machineSig:= HybridMachine.DryHybridMachine.DryHybridMachineSig)
      (sch, nil,
       DryHybridMachine.initial_machine
         (Sem := Clight_newSem ge)
         (permissions.getCurPerm init_mem)
        (initial_corestate CPROOF)) init_mem n) ->
  forall sch n,
    csafe
      (Sem := ClightSem ge)
      (ThreadPool:= threadPool.OrdinalPool.OrdinalThreadPool(Sem:=ClightSem ge))
      (machineSig:= HybridMachine.DryHybridMachine.DryHybridMachineSig)
      (sch, nil, (DryHybridMachine.initial_machine
         (Sem := ClightSem ge)
         (permissions.getCurPerm init_mem)
         initial_Clight_state)) init_mem n.
Proof.
  intros.
  eapply Clight_new_Clight_safety_gen; [|apply H|].
  { admit. (* globals_not_fresh *) }
  constructor; auto; intros; simpl.
  constructor.
  unfold initial_corestate, initial_Clight_state in *.
  destruct f_main as [? Hf]; destruct spr as (b & q & [? Hinit] & s); simpl in *.
  destruct (s O tt) as (jm & Hjm & _).
  specialize (Hinit _ Hjm) as (? & ? & Hinit & ?); subst; simpl in *.
  destruct (Genv.find_funct_ptr _ b); inv Hinit.
  inv Hf.
  constructor; simpl; auto.
  repeat constructor.
Admitted.

(*

Theorem Clight_initial_safe (sch : HybridMachineSig.schedule) (n : nat) :
    HybridMachineSig.HybridCoarseMachine.csafe
      (Sem := ClightSem ge)
      (ThreadPool:= threadPool.OrdinalPool.OrdinalThreadPool(Sem:=ClightSem ge))
      (machineSig:= HybridMachine.DryHybridMachine.DryHybridMachineSig)
      (sch, nil,
       DryHybridMachine.initial_machine(Sem := ClightSem ge)
                                       (permissions.getCurPerm init_mem)
        (initial_Clight_state CPROOF)) init_mem n.
  Proof.

 *)



End Clight_safety_equivalence.