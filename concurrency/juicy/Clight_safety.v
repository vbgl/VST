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
    MATCH_ST: forall (mtch_cnt: forall {tid},  containsThread tp tid -> containsThread tp' tid )
                (mtch_cnt': forall {tid}, containsThread tp' tid -> containsThread tp tid )
                (mtch_gtc: forall {tid} (Htid:containsThread tp tid)(Htid':containsThread tp' tid),
                    match_ctl (getThreadC Htid) (getThreadC Htid') )
                (mtch_gtr: forall {tid} (Htid:containsThread tp tid)(Htid':containsThread tp' tid),
                    getThreadR Htid = getThreadR Htid' )
                (mtch_locks: forall a, lockRes tp a = lockRes tp' a),
      match_st tp tp'.

Lemma MTCH_compat: forall js ds m,
    match_st js ds ->
    mem_compatible js m ->
    mem_compatible ds m.
Proof.
  intros ? ? ? MTCH mc.
  inv MTCH; inv mc; constructor; intros.
  - specialize (compat_th0 _ (mtch_cnt' _ cnt)).
    rewrite mtch_gtr with (Htid' := cnt) in compat_th0; auto.
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
  rewrite mtch_gtr with (Htid' := Htid'); auto.
Qed.

Lemma MTCH_invariant:
  forall js ds (MATCH : match_st js ds) (Hinv : invariant js), invariant ds.
Proof.
  intros; inv MATCH; inv Hinv; constructor; intros.
  - rewrite <- mtch_gtr with (Htid := mtch_cnt' _ cnti),
            <- mtch_gtr with (Htid := mtch_cnt' _ cntj); auto.
  - rewrite <- mtch_locks in *; eauto.
  - rewrite <- mtch_locks in *.
    rewrite <- mtch_gtr with (Htid := mtch_cnt' _ cnti); eauto.
  - specialize (thread_data_lock_coh0 _ (mtch_cnt' _ cnti)) as [].
    split; intros.
    + rewrite <- mtch_gtr with (Htid := mtch_cnt' _ cnti),
              <- mtch_gtr with (Htid := mtch_cnt' _ cntj); auto.
    + rewrite <- mtch_locks in *.
      rewrite <- mtch_gtr with (Htid := mtch_cnt' _ cnti); eauto.
  - rewrite <- mtch_locks in *.
    specialize (locks_data_lock_coh0 _ _ Hres) as [].
    split; intros.
    + rewrite <- mtch_gtr with (Htid := mtch_cnt' _ cntj); auto.
    + rewrite <- mtch_locks in *; eauto.
  - hnf in *.
    intros; specialize (lockRes_valid0 b ofs).
    rewrite mtch_locks in lockRes_valid0; destruct (lockRes _ _); auto.
    intro; rewrite <- mtch_locks; auto.
Qed.

Existing Instance scheduler.
Existing Instance DilMem.

Opaque updThread updThreadC containsThread getThreadC getThreadR.

Lemma Clight_new_Clight_safety_gen:
  forall n sch tr tp m tp',
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
    destruct (Genv.find_funct_ptr _ _) eqn: Hb; inv Hinit.
    destruct (Mem.alloc _ _ _) eqn: Halloc.
    eapply CoreSafe.
    { hnf; simpl.
      rewrite <- H5.
      change sch with (yield sch) at 2.
      eapply start_step; eauto; econstructor; eauto.
      { eapply MTCH_install_perm, Hperm. }
      { split.
        econstructor; eauto.
        - admit.
        - admit.
        - admit.
        - admit.
        - admit.
        - admit.
        - admit.
        - admit.
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
    pose proof (event_semantics.ev_step_ax1 _ _ _ _ _ _ Hcorestep) as Hstep; inv Hstep.
    { (* internal step *)
      inv H11; [|inv H1].
      inv H6; simpl in *.
      rewrite Hb in H16; inv H16.
      assert (vargs = [arg]); subst.
      { admit. (* cl_initial_core doesn't enforce that we provide the right number of arguments *) }
      eapply CoreSafe, csafe_reduce; [| eapply IHn; eauto | auto].
      - hnf; simpl.
        rewrite <- H5.
        change sch with (yield sch) at 4.
        change m'1 with (diluteMem m'1) at 2.
        eapply thread_step; eauto; econstructor; eauto.
        { admit. }
        { apply (gssThreadCode (mtch_cnt _ ctn)). }
        edestruct (event_semantics.ev_step_ax2 (@semSem (ClightSem ge))) as [ev' Hstep];
          [|assert (ev' = ev); [|subst; apply Hstep]].
        econstructor; auto.
        hnf; simpl.
        instantiate (1 := Clight.State _ _ _ _ _ _).
        unfold Clight.set_mem.
        apply Clight.step_internal_function.
        apply list_norepet_app in H18 as (? & ? & ?).
        constructor; eauto.
        { admit. }
        { admit. }
      - constructor; auto; intros.
        admit.
        admit. }
    { (* external call *)
      inv H14; [|inv H1].
      inv H6; simpl in *.
      rewrite Hb in H16; inv H16.
      assert (vargs = [arg]); subst.
      { admit. (* cl_initial_core doesn't enforce that we provide the right number of arguments *) }
      assert (ev = nil) by admit; subst.
      rewrite app_nil_r in Hsafe0.
      eapply IHn; eauto.
      { (* restrPermMap doesn't affect safety *)
        replace m0 with (restrPermMap (proj1 (Hcmpt0 tid0 Htid0))) at 1 by admit.
        apply Hsafe0. }
      { constructor; auto; intros.
        - destruct (eq_dec tid0 tid).
          + subst; rewrite !gssThreadCode.
            constructor; simpl.
            admit. (* Clight_new puts the arguments in the temp environment in the wrapper,
              so that they can be passed to the function, but this is fairly arbitrary. *)
          + (*pose proof (cntUpdate' _ _ ctn Htid0) as cntj.
            erewrite (gsoThreadCode _ ctn cntj) by auto.
            instantiate (1 := mtch_cnt _ Htid) in Htid'.
            pose proof (cntUpdate' _ _ _ Htid') as cntj'.
            unshelve erewrite (gsoThreadCode _ _ _ _ _ Htid'); auto.
            unshelve erewrite (gsoThreadCode _ _ _ _ _ cntj'); auto.*)
            admit.
        - admit. } }
    { inv Hstep; simpl in *; rewrite HschedN in HschedN0; inv HschedN0;
        try (inv Htstep; rewrite gssThreadCode in Hcode0; inv Hcode0);
        try match goal with H : sch = schedSkip sch |- _ =>
        symmetry in H; apply schedSkip_id in H; subst end; try discriminate; try contradiction.
      inv Hhalted; contradiction. }
  - (* In all other steps, the two semantics should trivially coincide...
       but of course they don't. *)
    inv Htstep.
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
    admit.
  - admit. (* should be able to reuse something from Clight_sem *)
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
      intro; eapply IHn.
      { eapply (csafe_reduce(ThreadPool := OrdinalPool.OrdinalThreadPool)); eauto. }
      constructor; auto; intros.
      destruct (eq_dec tid0 tid).
      - subst; rewrite !gssThreadCC.
        constructor.
        constructor; auto.
      - unshelve erewrite <- !gsoThreadCC; auto. }
  - inv Htstep.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
  - inv Hhalted; contradiction.
  - subst; eapply AngelSafe.
    { simpl; rewrite <- H5.
      eapply schedfail; eauto; simpl.
      - inv H0.
        intro; contradiction Htid; apply mtch_cnt'; auto.
      - eapply MTCH_invariant; eauto.
      - eapply MTCH_compat; eauto. }
    { intro; eapply IHn; eauto.
      eapply (csafe_reduce(ThreadPool := OrdinalPool.OrdinalThreadPool)); eauto.
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
  eapply Clight_new_Clight_safety_gen; [apply H|].
  constructor; auto; intros; simpl.
  constructor.
  unfold initial_corestate, initial_Clight_state in *.
  destruct f_main as [? Hf]; destruct spr as (b & q & [? Hinit] & s); simpl in *.
  destruct (s O tt) as (jm & Hjm & _).
  specialize (Hinit _ Hjm) as (? & ? & Hinit & ?); subst; simpl in *.
  destruct (Genv.find_funct_ptr _ _); inv Hinit.
  inv Hf.
  constructor; simpl; auto.
  repeat constructor.
Qed.

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