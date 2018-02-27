Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.lib.Integers.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import compcert.common.Events.
Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.

Require Import VST.msl.Extensionality.
Require Import VST.sepcomp.mem_lemmas.
Require Import VST.sepcomp.semantics.
Require Import VST.sepcomp.semantics_lemmas.

(** * Effect Semantics *)

(** Effect semantics augment memory semantics with effects, in the form
    of a set of locations [block -> Z -> bool] associated with each internal
    step of the semantics. *)

Record EffectSem {G C} :=
  { (** [sem] is a memory semantics. *)
    sem :> @MemSem G C

    (** The step relation of the new semantics. *)
  ; effstep: G -> (block -> Z -> bool) -> C -> mem -> C -> mem -> Prop

    (** The next three fields axiomatize [effstep] and its relation to the
        underlying step relation of [sem]. *)
  ; effax1: forall M g c m c' m',
       effstep g M c m c' m' ->
            corestep sem g c m c' m'
         /\ Mem.unchanged_on (fun b ofs => M b ofs = false) m m'
  ; effax2: forall g c m c' m',
       corestep sem g c m c' m' ->
       exists M, effstep g M c m c' m'
  ; effstep_perm: forall M g c m c' m',
       effstep g M c m c' m' ->
       forall b z, M b z = true -> Mem.perm m b z Cur Writable
  }.
(*
Arguments EffectSem [].
*)
(** * Lemmas and auxiliary definitions *)

Section effsemlemmas.
  Context {G C:Type} (Sem: @EffectSem G C) (g:G).

  Lemma effstep_valid: forall M c m c' m',
       effstep Sem g M c m c' m' ->
       forall b z, M b z = true -> Mem.valid_block m b.
  Proof. intros. eapply Mem.perm_valid_block. eapply effstep_perm; eassumption. Qed.

  Lemma effstep_corestep: forall M g c m c' m',
      effstep Sem g M c m c' m' -> corestep Sem g c m c' m'.
  Proof. intros. apply effax1 in H. apply H. Qed.

  Lemma effstep_unchanged: forall M g c m c' m',
        effstep Sem g M c m c' m' ->
        Mem.unchanged_on (fun b ofs => M b ofs = false) m m'.
  Proof. intros. apply effax1 in H. apply H. Qed.

  Lemma effstep_mem U c m c' m' (EF: effstep Sem g U c m c' m'): mem_step m m'.
  Proof. intros. apply effax1 in EF. destruct EF as [EF _].
         eapply corestep_mem. apply EF.
  Qed.

  Lemma effstep_fwd U c m c' m' (EF: effstep Sem g U c m c' m'): mem_forward m m'.
  Proof. apply preserve_mem. apply mem_forward_preserve.
         eapply effstep_mem. apply EF.
  Qed.

  Fixpoint effstepN (n:nat) : (block -> Z -> bool) -> C -> mem -> C -> mem -> Prop :=
    match n with
      | O => fun U c m c' m' => (c,m) = (c',m') /\ U = (fun b z => false)
      | S k => fun U c1 m1 c3 m3 => exists c2, exists m2, exists U1, exists U2,
        effstep Sem g U1 c1 m1 c2 m2 /\
        effstepN k U2 c2 m2 c3 m3 /\
        U = (fun b z => U1 b z || (U2 b z && valid_block_dec m1 b))
    end.

  Lemma effstepN_perm: forall n U c1 m1 c2 m2, effstepN n U c1 m1 c2 m2 ->
       forall b z, U b z = true -> Mem.perm m1 b z Cur Writable.
  Proof. intros n.
    induction n; simpl; intros. destruct H; subst. discriminate.
    destruct H as [c [m [U1 [U2 [Step [StepN UU]]]]]]; subst; simpl.
    specialize (IHn _ _ _ _ _ StepN).
    specialize (effstep_perm _ _ _ _ _ _ _ Step b z). intros.
    remember (U1 b z) as d.
    destruct d; simpl in *.
    + apply H; trivial.
    + (* destruct (Mem.perm_dec m1 b z Cur Writable). trivial. simpl in *.*)
      clear H Heqd StepN.
      rewrite andb_true_iff in H0. destruct H0.
      specialize (IHn _ _ H). destruct (valid_block_dec m1 b); inv H0.
      apply effstep_corestep in Step. apply corestep_mem in Step.
      apply perm_preserve in Step. apply Step; trivial.
      eapply Mem.perm_implies. eapply Mem.perm_max. eassumption. constructor.
  Qed.
  Lemma effstepN_valid n U c1 m1 c2 m2  (Step:effstepN n U c1 m1 c2 m2)
        b z (EFF:U b z = true): Mem.valid_block m1 b.
  Proof. eapply Mem.perm_valid_block. eapply effstepN_perm; eassumption. Qed.

  Lemma effstepN_mem: forall n U c m c' m' (EF: effstepN n U c m c' m'), mem_step m m'.
  Proof.
    induction n; simpl; intros.
    + destruct EF as [EF _]; inv EF. apply mem_step_refl.
    + destruct EF as [c1 [m2 [U1 [U2 [EF1 [EF2 _]]]]]].
      apply IHn in EF2. clear IHn.
      apply effstep_mem in EF1.
      eapply mem_step_trans; eassumption.
  Qed.

  Lemma effstepN_fwd n U c m c' m' (EF:effstepN n U c m c' m'): mem_forward m m'.
  Proof. apply preserve_mem. apply mem_forward_preserve.
         eapply effstepN_mem. apply EF.
  Qed.

  Lemma effstepN_corestepN: forall n E c m c' m',
      effstepN n E c m c' m' -> corestepN Sem g n c m c' m'.
  Proof. intros n.
    induction n; intros; simpl in *.
        apply H.
      destruct H as [c1 [m1 [U1 [U2 [Estep [EN HE]]]]]].
        apply effstep_corestep in Estep.
        apply IHn in EN. exists c1, m1.
        split; eassumption.
  Qed.

  Lemma effstepN_unchanged: forall n U c1 m1 c2 m2,
        effstepN n U c1 m1 c2 m2 ->
        Mem.unchanged_on (fun b z => U b z = false) m1 m2.
  Proof. intros n.
    induction n; simpl; intros.
      destruct H. inv H. apply Mem.unchanged_on_refl.
    rename c2 into c3. rename m2 into m3.
    destruct H as [c2 [m2 [E1 [E2 [Step1 [Step2 HE]]]]]].
    apply IHn in Step2; clear IHn. subst.
    assert (FWD:= effstep_fwd _ _ _ _ _ Step1).
    apply effstep_unchanged in Step1.
    split; intros.
     eapply Ple_trans; [apply Step1 | apply Step2].
     apply orb_false_iff in H. destruct H.
     remember (valid_block_dec m1 b) as v.
     destruct v; simpl in *; try contradiction.
     clear H0 Heqv.
     rewrite andb_true_r in H1.
     split; intros. apply Step2; trivial.
        apply (FWD _ v).
     apply Step1; try assumption.

     apply Step1; try assumption.
       apply Step2; try assumption.
        apply (FWD _ v).

   apply orb_false_iff in H. destruct H.
     remember (valid_block_dec m1 b) as v.
     destruct v; simpl in *; try contradiction.
     clear Heqv.
     rewrite andb_true_r in H1.
     destruct Step2. rewrite unchanged_on_contents; trivial.
       eapply Step1; try eassumption.
       eapply Step1; try eassumption.
     elim n0. eapply Mem.perm_valid_block; eassumption.
  Qed.

Lemma effstepN_trans: forall n1 n2 U1 st1 m1 st2 m2 U2 st3 m3,
      effstepN n1 U1 st1 m1 st2 m2 ->
      effstepN n2 U2 st2 m2 st3 m3 ->
   effstepN (n1+n2)
        (fun b z => U1 b z || (U2 b z && valid_block_dec m1 b)) st1 m1 st3 m3.
Proof. intros n1.
induction n1; simpl.
  intros. destruct H; subst. inv H. simpl.
  assert (U2 = (fun b z => U2 b z && valid_block_dec m2 b)).
    extensionality b; extensionality z.
    remember (U2 b z) as d. destruct d; trivial.
    apply eq_sym in Heqd.
    apply (effstepN_valid _ _ _ _ _ _ H0) in Heqd.
    remember (valid_block_dec m2 b) as q.
    destruct q; trivial. contradiction.
  rewrite H in H0. apply H0.
intros. rename st3 into st4. rename m3 into m4.
   rename st2 into st3. rename m2 into m3.
   rename U1 into U. rename U2 into U3.
   destruct H as [st2 [m2 [U1 [U2 [Step1 [Step2 HU]]]]]].
   subst; simpl in *.
   exists st2, m2, U1; simpl.
   specialize (IHn1 _ _ _ _ _ _ _ _ _ Step2 H0).
   clear Step2 H0.
   eexists; split. assumption.
   split. eassumption.
   extensionality b; extensionality z; simpl.
   remember (U1 b z) as d. destruct d; simpl; trivial; apply eq_sym in Heqd.
   remember (U2 b z) as q. destruct q; simpl; trivial; apply eq_sym in Heqq.
     remember (valid_block_dec m1 b) as u.
     destruct u; trivial; simpl. apply andb_false_r.
   remember (U3 b z) as p. destruct p; simpl; trivial; apply eq_sym in Heqp.
     remember (valid_block_dec m1 b) as u.
     destruct u; trivial; simpl. clear Hequ. rewrite andb_true_r.
       apply effstep_fwd in Step1. apply Step1 in v.
       destruct (valid_block_dec m2 b); trivial. destruct v; contradiction.
     rewrite andb_false_r. trivial.
Qed.

Lemma effstepN_trans': forall n1 n2 U U1 st1 m1 st2 m2 U2 st3 m3,
      effstepN n1 U1 st1 m1 st2 m2 ->
      effstepN n2 U2 st2 m2 st3 m3 ->
      U = (fun b z => U1 b z || (U2 b z && valid_block_dec m1 b)) ->
   effstepN (n1+n2) U st1 m1 st3 m3.
Proof. intros; subst. eapply effstepN_trans; eassumption. Qed.

  Definition effstep_plus U c m c' m' :=
    exists n, effstepN (S n) U c m c' m'.

  Definition effstep_star U c m c' m' :=
    exists n, effstepN n U c m c' m'.

  Lemma effstep_plus_corestep_plus U c m c' m' (EFF: effstep_plus U c m c' m'):
        corestep_plus Sem g c m c' m'.
  Proof. destruct EFF. apply effstepN_corestepN in H. exists x; trivial. Qed.

  Lemma effstep_star_corestep_star U c m c' m' (EFF: effstep_star U c m c' m'):
        corestep_star Sem g c m c' m'.
  Proof. destruct EFF. apply effstepN_corestepN in H. exists x; trivial. Qed.

  Lemma effstep_plus_star : forall U c1 c2 m1 m2,
    effstep_plus U c1 m1 c2 m2 -> effstep_star U c1 m1 c2 m2.
  Proof. intros. destruct H as [n1 H1]. eexists. apply H1. Qed.

  Lemma effstep_plus_trans : forall U1 c1 c2 c3 U2 m1 m2 m3,
    effstep_plus U1 c1 m1 c2 m2 -> effstep_plus U2 c2 m2 c3 m3 ->
    effstep_plus (fun b z => U1 b z || (U2 b z && valid_block_dec m1 b)) c1 m1 c3 m3.
  Proof. intros. destruct H as [n1 H1]. destruct H0 as [n2 H2].
    exists ((n1 + (S n2))%nat). simpl.
    apply (effstepN_trans (S n1) (S n2) U1 c1 m1 c2 m2 U2 c3 m3 H1 H2).
  Qed.
  Lemma effstep_plus_trans' : forall U U1 c1 c2 c3 U2 m1 m2 m3,
    effstep_plus U1 c1 m1 c2 m2 -> effstep_plus U2 c2 m2 c3 m3 ->
    U = (fun b z => U1 b z || (U2 b z && valid_block_dec m1 b)) ->
    effstep_plus U c1 m1 c3 m3.
  Proof. intros; subst. eapply effstep_plus_trans; eassumption. Qed.

  Lemma effstep_star_plus_trans : forall U1 c1 c2 c3 U2 m1 m2 m3,
    effstep_star U1 c1 m1 c2 m2 -> effstep_plus U2 c2 m2 c3 m3 ->
    effstep_plus (fun b z => U1 b z || (U2 b z && valid_block_dec m1 b)) c1 m1 c3 m3.
  Proof. intros. destruct H as [n1 H1]. destruct H0 as [n2 H2].
    exists ((n1 + n2)%nat).
    specialize (effstepN_trans n1 (S n2) U1 c1 m1 c2 m2 U2 c3 m3 H1 H2); intros H.
    rewrite <- plus_n_Sm in H. assumption.
  Qed.
  Lemma effstep_star_plus_trans' : forall U U1 c1 c2 c3 U2 m1 m2 m3,
    effstep_star U1 c1 m1 c2 m2 -> effstep_plus U2 c2 m2 c3 m3 ->
    U = (fun b z => U1 b z || (U2 b z && valid_block_dec m1 b)) ->
    effstep_plus U c1 m1 c3 m3.
  Proof. intros; subst. eapply effstep_star_plus_trans; eassumption. Qed.

  Lemma effstep_plus_star_trans: forall U1 c1 c2 c3 U2 m1 m2 m3,
    effstep_plus U1 c1 m1 c2 m2 -> effstep_star U2 c2 m2 c3 m3 ->
    effstep_plus (fun b z => U1 b z || (U2 b z && valid_block_dec m1 b)) c1 m1 c3 m3.
  Proof. intros. destruct H as [n1 H1]. destruct H0 as [n2 H2].
    exists ((n1 + n2)%nat).
    apply (effstepN_trans _ _  U1 c1 m1 c2 m2 U2 c3 m3 H1 H2).
  Qed.
  Lemma effstep_plus_star_trans': forall U U1 c1 c2 c3 U2 m1 m2 m3,
    effstep_plus U1 c1 m1 c2 m2 -> effstep_star U2 c2 m2 c3 m3 ->
    U = (fun b z => U1 b z || (U2 b z && valid_block_dec m1 b)) ->
    effstep_plus U c1 m1 c3 m3.
  Proof. intros; subst. eapply effstep_plus_star_trans; eassumption. Qed.

  Lemma effstep_star_trans: forall U1 c1 c2 c3 U2 m1 m2 m3,
    effstep_star U1 c1 m1 c2 m2 -> effstep_star U2 c2 m2 c3 m3 ->
    effstep_star (fun b z => U1 b z || (U2 b z && valid_block_dec m1 b)) c1 m1 c3 m3.
  Proof. intros. destruct H as [n1 H1]. destruct H0 as [n2 H2].
    eexists.
    eapply (effstepN_trans _ _ U1 c1 m1 c2 m2 U2 c3 m3 H1 H2).
  Qed.
  Lemma effstep_star_trans': forall U U1 c1 c2 c3 U2 m1 m2 m3,
    effstep_star U1 c1 m1 c2 m2 -> effstep_star U2 c2 m2 c3 m3 ->
    U = (fun b z => U1 b z || (U2 b z && valid_block_dec m1 b)) ->
    effstep_star U c1 m1 c3 m3.
  Proof. intros; subst. eapply effstep_star_trans; eassumption. Qed.

  Lemma effstep_plus_one: forall U c m c' m',
    effstep Sem g U c m c' m' -> effstep_plus U c m c' m'.
  Proof. intros. exists O. simpl. exists c', m', U, (fun b z =>false).
    intuition.
    extensionality b; extensionality z; simpl.
    rewrite orb_false_r. trivial.
  Qed.

  Lemma effstep_plus_two: forall U1 c m c' m' U2 c'' m'',
    effstep  Sem g U1 c m c' m' -> effstep Sem g U2 c' m' c'' m'' ->
    effstep_plus (fun b z => U1 b z || (U2 b z && valid_block_dec m b)) c m c'' m''.
  Proof. intros.
    exists (S O). exists c', m', U1, U2. split; trivial.
    split; trivial. simpl.
    exists c'', m'', U2, (fun b z =>false).
    intuition.
    extensionality b; extensionality z; simpl.
    rewrite orb_false_r. trivial.
  Qed.

  Lemma effstep_star_zero: forall c m, effstep_star (fun b z =>false) c m c m.
  Proof. intros. exists O. simpl. split; reflexivity. Qed.

  Lemma effstep_star_one: forall U c m c' m',
    effstep  Sem g U c m c' m' -> effstep_star U c m c' m'.
  Proof. intros.
    exists (S O). exists c', m', U, (fun b z =>false).
    simpl; split; trivial. split. split; reflexivity.
    extensionality b; extensionality z; simpl.
    rewrite orb_false_r. trivial.
  Qed.

  Lemma effstep_plus_split: forall U c m c' m',
    effstep_plus U c m c' m' ->
    exists c'', exists m'', exists U1, exists U2,
      effstep Sem g U1 c m c'' m'' /\
      effstep_star U2 c'' m'' c' m' /\
      U = (fun b z => U1 b z || (U2 b z && valid_block_dec m b)).
  Proof. intros.
    destruct H as [n [c2 [m2 [U1 [U2 [Hstep [Hstar HU]]]]]]].
    exists c2, m2, U1, U2. split. assumption. split; try assumption.
    exists n. assumption.
  Qed.

  Lemma effstep_plus_perm U c1 m1 c2 m2 (Step: effstep_plus U c1 m1 c2 m2):
       forall b z, U b z = true -> Mem.perm m1 b z Cur Writable.
  Proof. destruct Step. eapply effstepN_perm; eassumption. Qed.

  Lemma effstep_star_perm U c1 m1 c2 m2 (Step: effstep_star U c1 m1 c2 m2):
       forall b z, U b z = true -> Mem.perm m1 b z Cur Writable.
  Proof. destruct Step. eapply effstepN_perm; eassumption. Qed.

  Lemma effstep_plus_valid U c1 m1 c2 m2 (Step: effstep_plus U c1 m1 c2 m2):
       forall b z, U b z = true -> Mem.valid_block m1 b.
  Proof. destruct Step. eapply effstepN_valid; eassumption. Qed.

  Lemma effstep_star_valid U c1 m1 c2 m2 (Step: effstep_star U c1 m1 c2 m2):
       forall b z, U b z = true -> Mem.valid_block m1 b.
  Proof. destruct Step. eapply effstepN_valid; eassumption. Qed.

  Lemma effstep_star_mem U c m c' m' (EF: effstep_star U c m c' m'): mem_step m m'.
  Proof. destruct EF as [n H].
      eapply effstepN_mem; eassumption.
  Qed.

  Lemma effstep_plus_mem U c m c' m' (EF: effstep_plus U c m c' m'): mem_step m m'.
  Proof. destruct EF as [n H].
      eapply effstepN_mem; eassumption.
  Qed.

  Lemma effstep_plus_fwd U c m c' m' (EF: effstep_plus U c m c' m'): mem_forward m m'.
  Proof. apply preserve_mem. apply mem_forward_preserve.
         eapply effstep_plus_mem. apply EF.
  Qed.
  Lemma effstep_star_fwd U c m c' m' (EF: effstep_star U c m c' m'): mem_forward m m'.
  Proof. apply preserve_mem. apply mem_forward_preserve.
         eapply effstep_star_mem. apply EF.
  Qed.

  Lemma corestepN_effstepN: forall n c1 m1 c2 m2, corestepN Sem g n c1 m1 c2 m2 ->
       exists U, effstepN n U c1 m1 c2 m2.
  Proof. induction n; simpl; intros.
  + inv H. eexists; split; reflexivity.
  + destruct H as [c [m [Step Steps]]].
    apply effax2 in Step. destruct Step as [U1 HU1].
    destruct (IHn _ _ _ _ Steps) as [U2 HU2]; clear IHn Steps.
    do 5 eexists; split. eassumption. split. eassumption. reflexivity.
  Qed.
End effsemlemmas.


Definition EmptyEffect: Values.block -> Z -> bool := fun b z => false.

Lemma EmptyEffect_alloc: forall m lo hi m' b (ALLOC: Mem.alloc m lo hi = (m', b)),
      Mem.unchanged_on (fun b ofs => EmptyEffect b ofs = false) m m'.
Proof. intros.
       eapply Mem.alloc_unchanged_on; eassumption.
Qed.

Definition FreeEffect m lo hi (sp b:Values.block) (ofs:Z): bool :=
   if valid_block_dec m b
   then eq_block b sp && zle lo ofs && zlt ofs hi
   else false.

Lemma FreeEffectD: forall m lo hi sp b z
   (FREE:FreeEffect m lo hi sp b z = true),
   b = sp /\ Mem.valid_block m b /\ lo <= z /\ z < hi.
Proof. intros.
  unfold FreeEffect in FREE.
  destruct (valid_block_dec m b); simpl in *; try discriminate.
  destruct (eq_block b sp); subst; simpl in *; try discriminate.
  destruct (zle lo z); simpl in *; try discriminate.
  destruct (zlt z hi); simpl in *; try discriminate.
  auto.
Qed.

Lemma FreeEffect_free: forall m sp lo hi m'
             (FREE: Mem.free m sp lo hi = Some m'),
     Mem.unchanged_on  (fun b ofs => FreeEffect m lo hi sp b ofs = false) m m'.
Proof. intros.
       eapply Mem.free_unchanged_on; try eassumption.
               intros. unfold FreeEffect; simpl. intros N.
               destruct (valid_block_dec m sp).
               apply andb_false_iff in N. destruct H.
               destruct (eq_block sp sp); simpl in *.
                 destruct N. destruct (zle lo i). inv H1. xomega.
               destruct (zlt i hi). inv H1. xomega.
               apply n; trivial.
               apply Mem.free_range_perm in FREE.
                 apply n; clear n.
                 eapply Mem.perm_valid_block.
                 eapply (FREE lo). omega.
Qed.

Definition FreelistEffect
  m (L: list (Values.block * Z * Z)) (b:Values.block) (ofs:Z): bool :=
  List.fold_right (fun X E b z => match X with (bb,lo,hi) =>
                                   E b z || FreeEffect m lo hi bb b z
                                 end)
                  EmptyEffect L b ofs.

Lemma FreelistEffect_Dfalse: forall m bb lo hi L b ofs
      (F:FreelistEffect m ((bb, lo, hi) :: L) b ofs = false),
      FreelistEffect m L b ofs = false /\
      FreeEffect m lo hi bb b ofs = false.
Proof. intros.
  unfold FreelistEffect in F. simpl in F.
  apply orb_false_iff in F. apply F.
Qed.

Lemma FreelistEffect_Dtrue: forall m bb lo hi L b ofs
      (F:FreelistEffect m ((bb, lo, hi) :: L) b ofs = true),
      FreelistEffect m L b ofs = true \/
      FreeEffect m lo hi bb b ofs = true.
Proof. intros.
  unfold FreelistEffect in F. simpl in F.
  apply orb_true_iff in F. apply F.
Qed.

Lemma FreelistEffect_same: forall m bb lo hi mm L
          (F:Mem.free m bb lo hi = Some mm)
          b (VB: Mem.valid_block mm b) ofs,
      FreelistEffect mm L b ofs = false <-> FreelistEffect m L b ofs = false.
Proof. intros  m bb lo hi mm L.
  induction L; simpl; intros. intuition.
  intuition.
    apply orb_false_iff in H0. destruct H0.
    specialize (H _ VB ofs).
    apply H in H0. rewrite H0. simpl. clear H H0.
    unfold FreeEffect in *; simpl in *.
    apply Mem.nextblock_free in F.
    destruct (valid_block_dec m b).
      destruct (valid_block_dec mm b); trivial.
      red in v. rewrite <- F in v. elim n. apply v.
    trivial.
  apply orb_false_iff in H0. destruct H0.
    specialize (H _ VB ofs).
    apply H in H0. rewrite H0. simpl. clear H H0.
    unfold FreeEffect in *; simpl in *.
    apply Mem.nextblock_free in F.
    destruct (valid_block_dec mm b).
      destruct (valid_block_dec m b); trivial.
      red in v. rewrite F in v. elim n. apply v.
    trivial.
Qed.

Lemma FreelistEffect_freelist: forall L m m' (FL: Mem.free_list m L = Some m'),
      Mem.unchanged_on (fun b ofs => FreelistEffect m L b ofs = false) m m'.
Proof. intros L.
  induction L; simpl; intros.
    inv FL. apply Mem.unchanged_on_refl.
  destruct a as [[bb lo] hi].
    remember (Mem.free m bb lo hi) as d.
    destruct d; try inv FL. apply eq_sym in Heqd.
    specialize (IHL _ _ H0).
    assert (FF:= FreeEffect_free _ _ _ _ _ Heqd).
    eapply (unchanged_on_trans _ m0 _).
      eapply mem_unchanged_on_sub; try eassumption.
        intuition. apply orb_false_iff in H. apply H.
      clear FF.
      specialize (unchanged_on_validblock_invariant m0 m'
           (fun (b : block) (ofs : Z) => FreelistEffect m0 L b ofs = false)
           (fun (b : block) (ofs : Z) => FreelistEffect m L b ofs = false)).
      intros. apply H in IHL. clear H.
        eapply mem_unchanged_on_sub; try eassumption.
        intuition. apply orb_false_iff in H. apply H.
      clear IHL H. intros.
       eapply FreelistEffect_same; eassumption.
   eapply free_forward; eassumption.
Qed.

Lemma FreeEffect_validblock: forall m lo hi sp b ofs
        (EFF: FreeEffect m lo hi sp b ofs = true),
      Mem.valid_block m b.
Proof. intros.
  unfold FreeEffect in EFF.
  destruct (valid_block_dec m b); trivial; inv EFF.
Qed.

Lemma FreelistEffect_validblock: forall l m b ofs
        (EFF: FreelistEffect m l b ofs = true),
      Mem.valid_block m b.
Proof. intros l.
  induction l; unfold FreelistEffect; simpl; intros.
     unfold EmptyEffect in EFF. inv EFF.
  destruct a as [[bb lo] hi].
  apply orb_true_iff in EFF.
  destruct EFF.
  apply IHl in H. assumption.
  eapply FreeEffect_validblock; eassumption.
Qed.

Definition StoreEffect (tv:val)(vl : list memval) (b:Values.block) (z:Z):bool :=
  match tv with Vptr bb ofs => eq_block bb b &&
             zle (Ptrofs.unsigned ofs) z && zlt z (Ptrofs.unsigned ofs + Z.of_nat (length vl))
         | _ => false
  end.

Lemma StoreEffect_Storev: forall m chunk tv tv' m'
         (STORE : Mem.storev chunk m tv tv' = Some m'),
      Mem.unchanged_on
        (fun b ofs => StoreEffect tv (encode_val chunk tv') b ofs = false)
        m m'.
Proof. intros.
  destruct tv; inv STORE.
  unfold StoreEffect.
  split; intros.
      rewrite (Mem.nextblock_store _ _ _ _ _ _ H0); apply Ple_refl.
      split; intros. eapply Mem.perm_store_1; eassumption.
      eapply Mem.perm_store_2; eassumption.
  rewrite (Mem.store_mem_contents _ _ _ _ _ _ H0). clear H0.
  destruct (eq_block b b0); subst; simpl in *.
    rewrite PMap.gss. apply andb_false_iff in H.
    apply Mem.setN_outside.
    destruct H. destruct (zle (Ptrofs.unsigned i) ofs ); simpl in *. inv H.
                left. xomega.
    right. remember (Z.of_nat (length (encode_val chunk tv'))).
       destruct (zlt ofs (Ptrofs.unsigned i + z)); simpl in *. inv H. apply g.
  rewrite PMap.gso. trivial. intros N; subst. elim n; trivial.
Qed.

Lemma StoreEffectD: forall vaddr v b ofs
      (STE: StoreEffect vaddr v b ofs = true),
      exists i, vaddr = Vptr b i /\
        (Ptrofs.unsigned i) <= ofs < (Ptrofs.unsigned i + Z.of_nat (length v)).
Proof. intros.
  unfold StoreEffect in STE. destruct vaddr; inv STE.
  destruct (eq_block b0 b); inv H0.
  exists i.
  destruct (zle (Ptrofs.unsigned i) ofs); inv H1.
  destruct (zlt ofs (Ptrofs.unsigned i + Z.of_nat (length v))); inv H0.
  intuition.
Qed.

Lemma free_curWR m sp lo hi m' (FR: Mem.free m sp lo hi = Some m')
      b z (EFF: FreeEffect m lo hi sp b z = true):
      Mem.perm m b z Cur Writable.
Proof.
  apply FreeEffectD in EFF. destruct EFF as [? [? ?]]; subst.
  eapply Mem.perm_implies.
  eapply Mem.free_range_perm; eauto. constructor.
Qed.

Lemma storev_curWR ch m vaddr v m' (ST:Mem.storev ch m vaddr v = Some m')
      b z (EFF : StoreEffect vaddr (encode_val ch v) b z = true):
      Mem.perm m b z Cur Writable.
Proof.
  apply StoreEffectD in EFF. destruct EFF as [? [? [? ?]]]; subst.
  apply Mem.store_valid_access_3 in ST. apply ST.
  rewrite encode_val_length, <- size_chunk_conv in H1. omega.
Qed.

Lemma freelist_curWR l: forall m m' (FR: Mem.free_list m l = Some m')
      b z (EFF : FreelistEffect m l b z = true),
      Mem.perm m b z Cur Writable.
Proof. clear.
induction l; intros.
+ inv EFF.
+ destruct a as [[? ?] ?].
  simpl in FR.
  remember (Mem.free m b0 z0 z1) as f.
  destruct f; inv FR. symmetry in Heqf. simpl in EFF.
  remember (FreelistEffect m l b z) as q.
  destruct q; symmetry in Heqq; simpl in *.
  - clear EFF. specialize (IHl _ _ H0).
    remember (FreelistEffect m0 l b z) as w.
    destruct w; symmetry in Heqw.
    * eapply Mem.perm_free_3; eauto.
    * apply (FreelistEffect_same _ _ _ _ _ _ Heqf) in Heqw.
      rewrite Heqw in Heqq; discriminate.
      apply FreelistEffect_validblock in Heqq.
      eapply Mem.valid_block_free_1; eassumption.
  - eapply free_curWR; eassumption.
Qed.

Inductive MidStepEffectResult {C:Type} :=
  MSE_Ext: C -> mem -> (block -> Z -> bool) -> external_function -> list val -> MidStepEffectResult
| MSE_Ret: C -> mem -> (block -> Z -> bool) -> val -> MidStepEffectResult
| MSE_Div: (*(block -> Z -> bool) -> *)MidStepEffectResult. (*don't track written locations - ok for coarse grain, maybe not for instruction-level interleaving*)

Inductive midstepE {G C} (SEM : @EffectSem G C) g (c:C) (m:mem):
          @MidStepEffectResult C -> Prop:=
  mse_ext: forall c' m' W f args,
          effstep_star SEM g W c m c' m' ->
          at_external SEM c' = Some (f,args) ->
          midstepE SEM g c m (MSE_Ext c' m' W f args)
| mse_ret: forall c' m' W v,
          effstep_star SEM g W c m c' m' ->
          halted SEM c' = Some v ->
          midstepE SEM g c m (MSE_Ret c' m' W v)
| mse_div: forall (H: forall n, exists c' m', corestepN SEM g n c m c' m'),
          midstepE SEM g c m MSE_Div.
(*using effstep_star implies that we're not tracking writes to newly allocated blocks - 
  again this is sufficient for coarse interleaving but maybe not for fine*)


Section Tracksem.
  Context {G C:Type} (Sem: @EffectSem G C) (g:G).

  Fixpoint trackstepN (n:nat) : (block -> Z -> bool) -> C -> mem -> C -> mem -> Prop :=
    match n with
      | O => fun U c m c' m' => (c,m) = (c',m') /\ U = (fun b z => false)
      | S k => fun U c1 m1 c3 m3 => exists c2, exists m2, exists U1, exists U2,
        effstep Sem g U1 c1 m1 c2 m2 /\
        trackstepN k U2 c2 m2 c3 m3 /\
        U = (fun b z => U1 b z || U2 b z)
    end.

  Lemma trackstepN_effstepN
   (DET: forall c m c1 m1 U1 c2 m2 U2, effstep Sem g U1 c m c1 m1 -> 
         effstep Sem g U2 c m c2 m2 -> (c1,m1,U1)=(c2,m2,U2)):
  forall n c m c' m' W U,
  trackstepN n W c m c' m' -> effstepN Sem g n U c m c' m' ->
  U = fun b z => W b z && valid_block_dec m b.
  Proof. induction n; simpl; intros.
  + destruct H as [? ?]. inv H. 
    destruct H0 as [? ?]. inv H. simpl in *; trivial.
  + destruct H as [c1 [m1 [U1 [U2 [Estep [Tsteps HW]]]]]].
    destruct H0 as [c1' [m1' [U1' [U2' [Estep' [Esteps HU]]]]]].
    specialize (DET _ _ _ _ _ _ _ _ Estep' Estep). inv DET.
    specialize (IHn _ _ _ _ _ _ Tsteps Esteps); subst.
    extensionality b; extensionality z.
    remember (U1 b z) as q; symmetry in Heqq. destruct q; simpl in *.
    - exploit @effstep_valid. apply Estep. apply Heqq.
      destruct (valid_block_dec m b); trivial; simpl in *; congruence.
    - remember (U2 b z) as p; symmetry in Heqp. destruct p; simpl in *; [| congruence].
      destruct (valid_block_dec m1 b); simpl; trivial.
      destruct (valid_block_dec m b); simpl; trivial.
      elim n0. eapply effstep_fwd. eassumption.
      destruct (valid_block_dec m b); trivial; simpl in *; congruence.
Qed.

  Lemma trackstepN_effstep_iff:
  forall n c m c' m',
  (exists W, effstepN Sem g n W c m c' m') <-> (exists W, trackstepN n W c m c' m').
  Proof. induction n; simpl; intros.
  + split; trivial.
  + split; intros [W [cc [mm [U1 [U2 [Estep [Steps HW]]]]]]].
    - destruct (IHn cc mm c' m') as [X _].
      exploit X; clear X. exists U2; trivial. intros [U T].
      eexists; exists cc, mm; eexists; eexists. split. eassumption. 
      split. eassumption. reflexivity. 
    - destruct (IHn cc mm c' m') as [_ X].
      exploit X; clear X. exists U2; trivial. intros [U T].
      eexists; exists cc, mm; eexists; eexists. split. eassumption. 
      split. eassumption. reflexivity.
  Qed.

  Lemma trackstepN_perm: forall n U c1 m1 c2 m2, trackstepN n U c1 m1 c2 m2 ->
       forall b z, U b z = true -> Mem.valid_block m1 b -> Mem.perm m1 b z Cur Writable.
  Proof. intros n.
    induction n; simpl; intros. destruct H; subst. discriminate.
    destruct H as [c [m [U1 [U2 [Step [StepN UU]]]]]]; subst; simpl.
    specialize (IHn _ _ _ _ _ StepN).
    specialize (effstep_perm _ _ _ _ _ _ _ Step b z). intros.
    remember (U1 b z) as d.
    destruct d; simpl in *.
    + apply H; trivial.
    + clear H Heqd StepN.
      specialize (IHn _ _ H0).
      apply effstep_corestep in Step. apply corestep_mem in Step.
      apply perm_preserve in Step. apply Step; trivial.
      eapply Mem.perm_implies. eapply Mem.perm_max. apply IHn. apply Step. eassumption. constructor.
      apply IHn. apply Step. eassumption.
  Qed. 

  Lemma trackstepN_mem: forall n U c m c' m' (EF: trackstepN n U c m c' m'), mem_step m m'.
  Proof.
    induction n; simpl; intros.
    + destruct EF as [EF _]; inv EF. apply mem_step_refl.
    + destruct EF as [c1 [m2 [U1 [U2 [EF1 [EF2 _]]]]]].
      apply IHn in EF2. clear IHn.
      apply effstep_mem in EF1.
      eapply mem_step_trans; eassumption.
  Qed.

  Lemma trackstepN_fwd n U c m c' m' (EF:trackstepN n U c m c' m'): mem_forward m m'.
  Proof. apply preserve_mem. apply mem_forward_preserve.
         eapply trackstepN_mem. apply EF.
  Qed.

  Lemma trackstepN_valid' n: forall U c1 m1 c2 m2  (Step:trackstepN n U c1 m1 c2 m2)
        b z (EFF:U b z = true), Mem.valid_block m2 b. 
       (*Mem.valid_block m1 b may not hold - trackstep is also tracking writes to newly allocated blocks*)
  Proof. 
    induction n; simpl; intros. destruct Step; subst. discriminate.
    destruct Step as [c [m [U1 [U2 [Step [StepN UU]]]]]]; subst; simpl.
    specialize (IHn _ _ _ _ _ StepN).
    specialize (effstep_valid _ _ _ _ _ _ _ Step b z). intros.
    remember (U1 b z) as d; symmetry in Heqd.
    destruct d; simpl in *; eauto.
    eapply trackstepN_fwd. eassumption. eapply effstep_fwd. eassumption. apply H; trivial.
  Qed.

  Lemma trackstepN_corestepN: forall n E c m c' m',
      trackstepN n E c m c' m' -> corestepN Sem g n c m c' m'.
  Proof. intros n.
    induction n; intros; simpl in *.
        apply H.
      destruct H as [c1 [m1 [U1 [U2 [Estep [EN HE]]]]]].
        apply effstep_corestep in Estep.
        apply IHn in EN. exists c1, m1.
        split; eassumption.
  Qed.

  Lemma trackstepN_unchanged: forall n U c1 m1 c2 m2,
        trackstepN n U c1 m1 c2 m2 ->
        Mem.unchanged_on (fun b z => U b z = false) m1 m2.
  Proof. intros n.
    induction n; simpl; intros.
      destruct H. inv H. apply Mem.unchanged_on_refl.
    rename c2 into c3. rename m2 into m3.
    destruct H as [c2 [m2 [E1 [E2 [Step1 [Step2 HE]]]]]].
    apply IHn in Step2; clear IHn. subst.
    assert (FWD:= effstep_fwd _ _ _ _ _ _ _ Step1).
    apply effstep_unchanged in Step1.
    split; intros.
     eapply Ple_trans; [apply Step1 | apply Step2].
     apply orb_false_iff in H. destruct H.
     remember (valid_block_dec m1 b) as v.
     destruct v; simpl in *; try contradiction.
     clear H0 Heqv.
     split; intros. apply Step2; trivial.
        apply (FWD _ v).
     apply Step1; try assumption.

     apply Step1; try assumption.
       apply Step2; try assumption.
        apply (FWD _ v).

   apply orb_false_iff in H. destruct H.
     remember (valid_block_dec m1 b) as v.
     destruct v; simpl in *; try contradiction.
     clear Heqv.
     destruct Step2. rewrite unchanged_on_contents; trivial.
       eapply Step1; try eassumption.
       eapply Step1; try eassumption.
     elim n0. eapply Mem.perm_valid_block; eassumption.
  Qed.

  Lemma trackstepN_perm2: forall n U c1 m1 c2 m2, trackstepN n U c1 m1 c2 m2 ->
       forall b z, U b z = true -> Mem.perm m2 b z Cur Writable.
  (*does not hold -- location may have been freed after the write access later*)
  Abort. 

Lemma trackstepN_trans: forall n1 n2 U1 st1 m1 st2 m2 U2 st3 m3,
      trackstepN n1 U1 st1 m1 st2 m2 ->
      trackstepN n2 U2 st2 m2 st3 m3 ->
   trackstepN (n1+n2)
        (fun b z => U1 b z || U2 b z) st1 m1 st3 m3.
Proof. intros n1.
induction n1; simpl.
+ intros. destruct H; subst. inv H. simpl. trivial.
+ intros. rename st3 into st4. rename m3 into m4.
   rename st2 into st3. rename m2 into m3.
   rename U1 into U. rename U2 into U3.
   destruct H as [st2 [m2 [U1 [U2 [Step1 [Step2 HU]]]]]].
   subst; simpl in *.
   exists st2, m2, U1; simpl.
   specialize (IHn1 _ _ _ _ _ _ _ _ _ Step2 H0).
   clear Step2 H0.
   eexists; split. assumption.
   split. eassumption.
   extensionality b; extensionality z; simpl. rewrite orb_assoc; trivial.
Qed.

Lemma trackstepN_trans': forall n1 n2 U U1 st1 m1 st2 m2 U2 st3 m3,
      trackstepN n1 U1 st1 m1 st2 m2 ->
      trackstepN n2 U2 st2 m2 st3 m3 ->
      U = (fun b z => U1 b z || U2 b z) ->
   trackstepN (n1+n2) U st1 m1 st3 m3.
Proof. intros; subst. eapply trackstepN_trans; eassumption. Qed.

  Definition trackstep_plus U c m c' m' :=
    exists n, trackstepN (S n) U c m c' m'.

  Definition trackstep_star U c m c' m' :=
    exists n, trackstepN n U c m c' m'.

  Lemma trackstep_plus_corestep_plus U c m c' m' (EFF: trackstep_plus U c m c' m'):
        corestep_plus Sem g c m c' m'.
  Proof. destruct EFF. apply trackstepN_corestepN in H. exists x; trivial. Qed.

  Lemma trackstep_star_corestep_star U c m c' m' (EFF: trackstep_star U c m c' m'):
        corestep_star Sem g c m c' m'.
  Proof. destruct EFF. apply trackstepN_corestepN in H. exists x; trivial. Qed.

  Lemma trackstep_plus_star : forall U c1 c2 m1 m2,
    trackstep_plus U c1 m1 c2 m2 -> trackstep_star U c1 m1 c2 m2.
  Proof. intros. destruct H as [n1 H1]. eexists. apply H1. Qed.

  Lemma trackstep_plus_trans : forall U1 c1 c2 c3 U2 m1 m2 m3,
    trackstep_plus U1 c1 m1 c2 m2 -> trackstep_plus U2 c2 m2 c3 m3 ->
    trackstep_plus (fun b z => U1 b z || U2 b z) c1 m1 c3 m3.
  Proof. intros. destruct H as [n1 H1]. destruct H0 as [n2 H2].
    exists ((n1 + (S n2))%nat). simpl.
    apply (trackstepN_trans (S n1) (S n2) U1 c1 m1 c2 m2 U2 c3 m3 H1 H2).
  Qed.
  Lemma trackstep_plus_trans' : forall U U1 c1 c2 c3 U2 m1 m2 m3,
    trackstep_plus U1 c1 m1 c2 m2 -> trackstep_plus U2 c2 m2 c3 m3 ->
    U = (fun b z => U1 b z || U2 b z) ->
    trackstep_plus U c1 m1 c3 m3.
  Proof. intros; subst. eapply trackstep_plus_trans; eassumption. Qed.

  Lemma trackstep_star_plus_trans : forall U1 c1 c2 c3 U2 m1 m2 m3,
    trackstep_star U1 c1 m1 c2 m2 -> trackstep_plus U2 c2 m2 c3 m3 ->
    trackstep_plus (fun b z => U1 b z || U2 b z) c1 m1 c3 m3.
  Proof. intros. destruct H as [n1 H1]. destruct H0 as [n2 H2].
    exists ((n1 + n2)%nat).
    specialize (trackstepN_trans n1 (S n2) U1 c1 m1 c2 m2 U2 c3 m3 H1 H2); intros H.
    rewrite <- plus_n_Sm in H. assumption.
  Qed.
  Lemma trackstep_star_plus_trans' : forall U U1 c1 c2 c3 U2 m1 m2 m3,
    trackstep_star U1 c1 m1 c2 m2 -> trackstep_plus U2 c2 m2 c3 m3 ->
    U = (fun b z => U1 b z || U2 b z) ->
    trackstep_plus U c1 m1 c3 m3.
  Proof. intros; subst. eapply trackstep_star_plus_trans; eassumption. Qed.

  Lemma trackstep_plus_star_trans: forall U1 c1 c2 c3 U2 m1 m2 m3,
    trackstep_plus U1 c1 m1 c2 m2 -> trackstep_star U2 c2 m2 c3 m3 ->
    trackstep_plus (fun b z => U1 b z || U2 b z) c1 m1 c3 m3.
  Proof. intros. destruct H as [n1 H1]. destruct H0 as [n2 H2].
    exists ((n1 + n2)%nat).
    apply (trackstepN_trans _ _  U1 c1 m1 c2 m2 U2 c3 m3 H1 H2).
  Qed.
  Lemma trackstep_plus_star_trans': forall U U1 c1 c2 c3 U2 m1 m2 m3,
    trackstep_plus U1 c1 m1 c2 m2 -> trackstep_star U2 c2 m2 c3 m3 ->
    U = (fun b z => U1 b z || U2 b z) ->
    trackstep_plus U c1 m1 c3 m3.
  Proof. intros; subst. eapply trackstep_plus_star_trans; eassumption. Qed.

  Lemma trackstep_star_trans: forall U1 c1 c2 c3 U2 m1 m2 m3,
    trackstep_star U1 c1 m1 c2 m2 -> trackstep_star U2 c2 m2 c3 m3 ->
    trackstep_star (fun b z => U1 b z || U2 b z) c1 m1 c3 m3.
  Proof. intros. destruct H as [n1 H1]. destruct H0 as [n2 H2].
    eexists.
    eapply (trackstepN_trans _ _ U1 c1 m1 c2 m2 U2 c3 m3 H1 H2).
  Qed.
  Lemma trackstep_star_trans': forall U U1 c1 c2 c3 U2 m1 m2 m3,
    trackstep_star U1 c1 m1 c2 m2 -> trackstep_star U2 c2 m2 c3 m3 ->
    U = (fun b z => U1 b z || U2 b z) ->
    trackstep_star U c1 m1 c3 m3.
  Proof. intros; subst. eapply trackstep_star_trans; eassumption. Qed.

  Lemma trackstep_plus_one: forall U c m c' m',
    effstep Sem g U c m c' m' -> trackstep_plus U c m c' m'.
  Proof. intros. exists O. simpl. exists c', m', U, (fun b z =>false).
    intuition.
    extensionality b; extensionality z; simpl.
    rewrite orb_false_r. trivial.
  Qed.

  Lemma trackstep_plus_two: forall U1 c m c' m' U2 c'' m'',
    effstep  Sem g U1 c m c' m' -> effstep Sem g U2 c' m' c'' m'' ->
    trackstep_plus (fun b z => U1 b z || U2 b z) c m c'' m''.
  Proof. intros.
    exists (S O). exists c', m', U1, U2. split; trivial.
    split; trivial. simpl.
    exists c'', m'', U2, (fun b z =>false).
    intuition.
    extensionality b; extensionality z; simpl.
    rewrite orb_false_r. trivial.
  Qed.

  Lemma trackstep_star_zero: forall c m, trackstep_star (fun b z =>false) c m c m.
  Proof. intros. exists O. simpl. split; reflexivity. Qed.

  Lemma trackstep_star_one: forall U c m c' m',
    effstep  Sem g U c m c' m' -> trackstep_star U c m c' m'.
  Proof. intros.
    exists (S O). exists c', m', U, (fun b z =>false).
    simpl; split; trivial. split. split; reflexivity.
    extensionality b; extensionality z; simpl.
    rewrite orb_false_r. trivial.
  Qed.

  Lemma trackstep_plus_split: forall U c m c' m',
    trackstep_plus U c m c' m' ->
    exists c'', exists m'', exists U1, exists U2,
      effstep Sem g U1 c m c'' m'' /\
      trackstep_star U2 c'' m'' c' m' /\
      U = (fun b z => U1 b z || U2 b z).
  Proof. intros.
    destruct H as [n [c2 [m2 [U1 [U2 [Hstep [Hstar HU]]]]]]].
    exists c2, m2, U1, U2. split. assumption. split; try assumption.
    exists n. assumption.
  Qed.

  Lemma trackstep_plus_perm U c1 m1 c2 m2 (Step: trackstep_plus U c1 m1 c2 m2):
       forall b z, U b z = true -> Mem.valid_block m1 b -> Mem.perm m1 b z Cur Writable.
  Proof. destruct Step. eapply trackstepN_perm; eassumption. Qed.

  Lemma trackstep_star_perm U c1 m1 c2 m2 (Step: trackstep_star U c1 m1 c2 m2):
       forall b z, U b z = true -> Mem.valid_block m1 b -> Mem.perm m1 b z Cur Writable.
  Proof. destruct Step. eapply trackstepN_perm; eassumption. Qed.

  Lemma trackstep_plus_valid' U c1 m1 c2 m2 (Step: trackstep_plus U c1 m1 c2 m2):
       forall b z, U b z = true -> Mem.valid_block m2 b.
  Proof. destruct Step. eapply trackstepN_valid'; eassumption. Qed.

  Lemma trackstep_star_valid' U c1 m1 c2 m2 (Step: trackstep_star U c1 m1 c2 m2):
       forall b z, U b z = true -> Mem.valid_block m2 b.
  Proof. destruct Step. eapply trackstepN_valid'; eassumption. Qed.

  Lemma trackstep_star_mem U c m c' m' (EF: trackstep_star U c m c' m'): mem_step m m'.
  Proof. destruct EF as [n H].
      eapply trackstepN_mem; eassumption.
  Qed.

  Lemma trackstep_plus_mem U c m c' m' (EF: trackstep_plus U c m c' m'): mem_step m m'.
  Proof. destruct EF as [n H].
      eapply trackstepN_mem; eassumption.
  Qed.

  Lemma trackstep_plus_fwd U c m c' m' (EF: trackstep_plus U c m c' m'): mem_forward m m'.
  Proof. apply preserve_mem. apply mem_forward_preserve.
         eapply trackstep_plus_mem. apply EF.
  Qed.
  Lemma trackstep_star_fwd U c m c' m' (EF: trackstep_star U c m c' m'): mem_forward m m'.
  Proof. apply preserve_mem. apply mem_forward_preserve.
         eapply trackstep_star_mem. apply EF.
  Qed.

  Lemma trackstep_star_unchanged U c1 m1 c2 m2 (T: trackstep_star U c1 m1 c2 m2):
        Mem.unchanged_on (fun b z => U b z = false) m1 m2.
  Proof. destruct T. apply trackstepN_unchanged in H; trivial. Qed.

  Lemma trackstep_plus_unchanged U c1 m1 c2 m2 (T: trackstep_plus U c1 m1 c2 m2):
        Mem.unchanged_on (fun b z => U b z = false) m1 m2.
  Proof. destruct T. apply trackstepN_unchanged in H; trivial. Qed.

End Tracksem.
(*
Require Import VST.concurrency.paco.src.paco.

Section TRACKDIV.
  Context {G C:Type} (Sem: @EffectSem G C) (g:G). 

  CoInductive trackdiv: C -> mem -> (block -> Z -> bool) -> Prop :=
  | Trackdiv: forall c m W c1 m1 U V, effstep Sem g W c m c1 m1 -> trackdiv c1 m1 U ->
              V =(fun b z => W b z || U b z) ->
            trackdiv c m V.

  Variable R: C -> mem -> (block -> Z -> bool) -> Prop.

  Hypothesis TrackCase : forall c m V, R c m V -> 
    exists U W c1 m1, effstep Sem g W c m c1 m1 /\ trackdiv c1 m1 U  /\ 
                      V = (fun b z => W b z || U b z).

  Theorem track_coind : forall c m V, R c m V -> trackdiv c m V. 
  Proof. cofix; intros. clear track_coind. 
     destruct (TrackCase _ _ _ H) as [U [W [c1 [m1 [Step [Steps HV]]]]]]; subst.
     econstructor; eauto.
  Qed.

  Lemma trackdiv_perm: forall c m W (Step: trackdiv c m W) b z,
      W b z = true -> Mem.valid_block m b -> Mem.perm m b z Cur Writable.
  Proof. intros. pinversion Step. punfold Step. pcofix Step. intros c m W Step. inversion Step; subst. cofix. Step. inv Step. rename W0 into W.
    remember (W b z) as w; symmetry in Heqw; destruct w; simpl in H.
  + eapply effstep_perm; eauto.
  + apply effstep_unchanged in H1. apply H1; trivial; clear H1. 
     Check track_coind.

End TRACKDIV.
*)

Inductive MidStepTrackResult {C:Type} :=
  MST_Ext: C -> mem -> (block -> Z -> bool) -> external_function -> list val -> MidStepTrackResult
| MST_Ret: C -> mem -> (block -> Z -> bool) -> val -> MidStepTrackResult
| MST_Div: (block -> Z -> Prop) -> MidStepTrackResult. (*DO track written locations*)

Inductive midstepT {G C} (SEM : @EffectSem G C) g (c:C) (m:mem):
          @MidStepTrackResult C -> Prop:=
  mst_ext: forall c' m' W f args,
          trackstep_star SEM g W c m c' m' ->
          at_external SEM c' = Some (f,args) ->
          midstepT SEM g c m (MST_Ext c' m' W f args)
| mst_ret: forall c' m' W v,
          trackstep_star SEM g W c m c' m' ->
          halted SEM c' = Some v ->
          midstepT SEM g c m (MST_Ret c' m' W v)
(*| mst_div: forall W, trackdiv SEM g c m W ->
           midstepT SEM g c m (MST_Div W).*)
| mst_div: forall W (U : nat -> block -> Z -> bool)
               (ci: nat -> C) (mi: nat -> mem)
               (Steps: forall i, trackstepN SEM g i (U i) c m (ci i) (mi i))
               (HW: forall b z, W b z <-> exists i, U i b z = true)
               (H: (ci O, mi O) = (c,m)),
          midstepT SEM g c m (MST_Div W).
(*Alternative definition of last case using individual tracksteps:
| mst_div: forall W (U : nat -> block -> Z -> bool)
               (ci: nat -> C) (mi: nat -> mem)
               (Steps: forall i, trackstepN SEM g 1 (U i) (ci i) (mi i) (ci (S i)) (mi (S i)))
               (HW: forall b z, W b z = true <-> exists i, U i b z = true)
               (H: (ci O, mi O) = (c,m)),
          midstepT SEM g c m (MST_Div W).*)

Definition Wset {C} (R:@MidStepTrackResult C) : (block -> Z -> Prop) :=
  match R with
    MST_Ext _ _ W _ _ => (fun b z => W b z = true)
  | MST_Ret _ _ W _ => (fun b z => W b z = true)
  | MST_Div W => W
  end.

  Lemma midstepT_perm {G C} (SEM : @EffectSem G C) g c1 m1 R (Step: midstepT SEM g c1 m1 R):
       forall b z, Wset R b z -> Mem.valid_block m1 b -> Mem.perm m1 b z Cur Writable.
  Proof. destruct Step; simpl.
    + eapply trackstep_star_perm; eassumption.
    + eapply trackstep_star_perm; eassumption.
    + intros. apply HW in H0. destruct H0 as [i I].
      eapply trackstepN_perm; eauto. 
  Qed.

Definition MST_unchanged_on {C} m (A: @MidStepTrackResult C) :=
  match A with
    MST_Ext _ m' W _ _ => Mem.unchanged_on (fun b z => W b z = false) m m'
  | MST_Ret _ m' W  _ => Mem.unchanged_on (fun b z => W b z = false) m m'
  | MST_Div _ => True
  end.

  Lemma midstepT_unchanged {G C} (SEM : @EffectSem G C) g c1 m1 R (Step: midstepT SEM g c1 m1 R):
        MST_unchanged_on m1 R.
  Proof. inv Step; simpl; trivial; eapply trackstep_star_unchanged; eassumption. Qed.

Lemma corestepN_midstepT_atExt {G C} (SEM : @EffectSem G C) g: forall n c1 m1 c2 m2 f args,
   corestepN SEM g n c1 m1 c2 m2 -> at_external SEM c2 = Some (f,args) ->
   exists W, midstepT SEM g c1 m1 (MST_Ext c2 m2 W f args) /\
             forall b z, W b z = true -> Mem.valid_block m1 b -> Mem.perm m1 b z Cur Writable.
Proof. intros.
  apply corestepN_effstepN in H. destruct H as [U EFF].
  destruct (trackstepN_effstep_iff SEM g n c1 m1 c2 m2) as [X _].
  exploit X; clear X. eexists; eassumption. intros [W HW]. clear EFF.
  eexists; split. econstructor. exists n; apply HW. trivial.
  eapply trackstepN_perm; eassumption.
Qed. 

Lemma corestepN_midstepT_Ret {G C} (SEM : @EffectSem G C) g: forall n c1 m1 c2 m2 v,
   corestepN SEM g n c1 m1 c2 m2 -> halted SEM c2 = Some v ->
   exists W, midstepT SEM g c1 m1 (MST_Ret c2 m2 W v) /\
             forall b z, W b z = true -> Mem.valid_block m1 b -> Mem.perm m1 b z Cur Writable.
Proof. intros.
  apply corestepN_effstepN in H. destruct H as [U EFF].
  destruct (trackstepN_effstep_iff SEM g n c1 m1 c2 m2) as [X _].
  exploit X; clear X. eexists; eassumption. intros [W HW]. clear EFF.
  eexists; split. econstructor. exists n; apply HW. trivial.
  eapply trackstepN_perm; eassumption.
Qed.

Require Import Coq.Logic.ChoiceFacts.

(*Of course, some writes in the diverging exection (DE) may be to locations in 
blocks that are only allocated during DE.
But these locations are not shared with other threads (since DE does not make external calls).
So they can;t participate in races, so coarse-to-fine-proof should be ok.
Also not that the shared/nonshared info of locations in blocks valid in m1 never changes, 
again because DE doe not contain lock/unlock calls.*)
Lemma corestepN_midstepT_Div {G C} (FCC: FunctionalChoice_on nat C)
   (FCM: FunctionalChoice_on nat mem) (FCW: FunctionalChoice_on nat (block -> Z -> bool))
   (SEM : @EffectSem G C) g: forall c1 m1,
   (forall n, exists c2 m2, corestepN SEM g n c1 m1 c2 m2) -> 
   exists W, midstepT SEM g c1 m1 (MST_Div W) /\
             forall b z, W b z -> Mem.valid_block m1 b -> Mem.perm m1 b z Cur Writable.
Proof. intros.
  assert (ESTEPS: forall n : nat,
    exists (c2 : C) (m2 : mem) Wn, effstepN SEM g n Wn c1 m1 c2 m2).
  { intros. destruct (H n) as [c2 [m2 STEP]]. exists c2, m2.
    apply corestepN_effstepN in STEP; trivial. }
  clear H.
  destruct (FCC _ ESTEPS) as [fC HC]; clear ESTEPS.
  destruct (FCM _ HC) as [fM HM]; clear HC.
  assert (HT: forall n, exists W, trackstepN SEM g n W c1 m1 (fC n) (fM n)).
  { intros. apply (trackstepN_effstep_iff SEM g n c1 m1 (fC n) (fM n)); trivial. } 
  destruct (FCW _ HT) as [fU HU]; clear HT HM.
  exists (fun b z => exists i, fU i b z = true); split.
  + econstructor. eassumption. intros; split; trivial.
    specialize (HU O). destruct HU as [Q _]; rewrite Q; trivial.
  + intros. destruct H as [i I]. specialize (HU i).
    eapply trackstepN_perm; eassumption.
Qed.
(*
------
Inductive MidStepTrackResult {C:Type} :=
  MST_Ext: C -> mem -> (block -> Z -> bool) -> external_function -> list val -> MidStepTrackResult
| MST_Ret: C -> mem -> (block -> Z -> bool) -> val -> MidStepTrackResult
| MST_Div: (block -> Z -> bool) -> MidStepTrackResult. (*DO track written locations*)

Inductive midstepT {G C} (SEM : @EffectSem G C) g (c:C) (m:mem):
          @MidStepTrackResult C -> Prop:=
  mst_ext: forall c' m' W f args,
          trackstep_star SEM g W c m c' m' ->
          at_external SEM c' = Some (f,args) ->
          midstepT SEM g c m (MST_Ext c' m' W f args)
| mst_ret: forall c' m' W v,
          trackstep_star SEM g W c m c' m' ->
          halted SEM c' = Some v ->
          midstepT SEM g c m (MST_Ret c' m' W v)
| mst_div: forall W (U : nat -> block -> Z -> bool)
               (ci: nat -> C) (mi: nat -> mem)
               (Steps: forall i, trackstepN SEM g i (U i) c m (ci i) (mi i))
               (HW: forall b z, W b z = true <-> exists i, U i b z = true)
               (H: (ci O, mi O) = (c,m)),
          midstepT SEM g c m (MST_Div W).
(*Alternative definition of last case unsing individual tracksteps:
| mst_div: forall W (U : nat -> block -> Z -> bool)
               (ci: nat -> C) (mi: nat -> mem)
               (Steps: forall i, trackstepN SEM g 1 (U i) (ci i) (mi i) (ci (S i)) (mi (S i)))
               (HW: forall b z, W b z = true <-> exists i, U i b z = true)
               (H: (ci O, mi O) = (c,m)),
          midstepT SEM g c m (MST_Div W).*)

Definition Wset {C} (R:@MidStepTrackResult C) : (block -> Z -> bool) :=
  match R with
    MST_Ext _ _ W _ _ => W
  | MST_Ret _ _ W _ => W
  | MST_Div W => W
  end.

  Lemma midstepT_perm {G C} (SEM : @EffectSem G C) g c1 m1 R (Step: midstepT SEM g c1 m1 R):
       forall b z, Wset R b z = true -> Mem.valid_block m1 b -> Mem.perm m1 b z Cur Writable.
  Proof. destruct Step; simpl.
    + eapply trackstep_star_perm; eassumption.
    + eapply trackstep_star_perm; eassumption.
    + intros. apply HW in H0. destruct H0 as [i I].
      eapply trackstepN_perm; eauto. 
  Qed.

Definition MST_unchanged_on {C} m (A: @MidStepTrackResult C) :=
  match A with
    MST_Ext _ m' W _ _ => Mem.unchanged_on (fun b z => W b z = false) m m'
  | MST_Ret _ m' W  _ => Mem.unchanged_on (fun b z => W b z = false) m m'
  | MST_Div _ => True
  end.

  Lemma midstepT_unchanged {G C} (SEM : @EffectSem G C) g c1 m1 R (Step: midstepT SEM g c1 m1 R):
        MST_unchanged_on m1 R.
  Proof. inv Step; simpl; trivial; eapply trackstep_star_unchanged; eassumption. Qed.

Lemma corestepN_midstepT_atExt {G C} (SEM : @EffectSem G C) g: forall n c1 m1 c2 m2 f args,
   corestepN SEM g n c1 m1 c2 m2 -> at_external SEM c2 = Some (f,args) ->
   exists W, midstepT SEM g c1 m1 (MST_Ext c2 m2 W f args) /\
             forall b z, W b z = true -> Mem.valid_block m1 b -> Mem.perm m1 b z Cur Writable.
Proof. intros.
  apply corestepN_effstepN in H. destruct H as [U EFF].
  destruct (trackstepN_effstep_iff SEM g n c1 m1 c2 m2) as [X _].
  exploit X; clear X. eexists; eassumption. intros [W HW]. clear EFF.
  eexists; split. econstructor. exists n; apply HW. trivial.
  eapply trackstepN_perm; eassumption.
Qed. 

Lemma corestepN_midstepT_Ret {G C} (SEM : @EffectSem G C) g: forall n c1 m1 c2 m2 v,
   corestepN SEM g n c1 m1 c2 m2 -> halted SEM c2 = Some v ->
   exists W, midstepT SEM g c1 m1 (MST_Ret c2 m2 W v) /\
             forall b z, W b z = true -> Mem.valid_block m1 b -> Mem.perm m1 b z Cur Writable.
Proof. intros.
  apply corestepN_effstepN in H. destruct H as [U EFF].
  destruct (trackstepN_effstep_iff SEM g n c1 m1 c2 m2) as [X _].
  exploit X; clear X. eexists; eassumption. intros [W HW]. clear EFF.
  eexists; split. econstructor. exists n; apply HW. trivial.
  eapply trackstepN_perm; eassumption.
Qed. 

Require Import Coq.Logic.ChoiceFacts.

Lemma corestepN_midstepT_Div {G C} (FCC: FunctionalChoice_on nat C)
   (FCM: FunctionalChoice_on nat mem) (FCW: FunctionalChoice_on nat (block -> Z -> bool))
   (FF: FunctionalRelReification_on (block * Z) (block -> Z -> bool))
   (SEM : @EffectSem G C) g: forall c1 m1,
   (forall n, exists c2 m2, corestepN SEM g n c1 m1 c2 m2) -> 
   exists W, midstepT SEM g c1 m1 (MST_Div W) /\
             forall b z, W b z = true -> Mem.valid_block m1 b -> Mem.perm m1 b z Cur Writable.
Proof. intros.
  assert (ESTEPS: forall n : nat,
    exists (c2 : C) (m2 : mem) Wn, effstepN SEM g n Wn c1 m1 c2 m2).
  { intros. destruct (H n) as [c2 [m2 STEP]]. exists c2, m2.
    apply corestepN_effstepN in STEP; trivial. }
  clear H.
  destruct (FCC _ ESTEPS) as [fC HC]; clear ESTEPS.
  destruct (FCM _ HC) as [fM HM]; clear HC.
  assert (HT: forall n, exists W, trackstepN SEM g n W c1 m1 (fC n) (fM n)).
  { intros. apply (trackstepN_effstep_iff SEM g n c1 m1 (fC n) (fM n)); trivial. } 
  destruct (FCW _ HT) as [fU HU]; clear HT HM. 
  assert (HW: exists W: block -> Z -> bool, forall b z, W b z = true <-> exists i, fU i b z = true).
  { clear HU g c1 m1 fC fM.
Check Mem.unchanged_on.
    destruct (FF (fun bz f => exists i, fU i (fst bz) (snd bz) = true)).
    + intros [b z]. simpl. admit.
    + }
  destruct HW as [W HW].
  exists W; split.
  + econstructor. eassumption. trivial.
    specialize (HU O). destruct HU as [Q _]; rewrite Q; trivial.
  + intros. apply HW in H. destruct H as [i I]. specialize (HU i).
    eapply trackstepN_perm; eassumption.
Qed. 
  
------
Definition addeffect {C} m (U:block -> Z -> bool) (R: @MidStepEffectResult C) :=
  match R with
    MSE_Ext c' m' W f args => MSE_Ext c' m' (fun b z => U b z || W b z  && valid_block_dec m b)  f args
  | MSE_Ret c' m' W v => MSE_Ret c' m' (fun b z => U b z || W b z  && valid_block_dec m b) v
  | MSE_Div => MSE_Div
  end.

Lemma midtepE_preserves_trackstep_rev {G C} (SEM : @EffectSem G C) g:
   forall c m  U c' m', trackstep SEM g U c m c' m' ->
   forall R, midstepE SEM g c' m' R -> midstepE SEM g c m (addeffect m U R).
Proof. intros. inv H0.
+ constructor; trivial. destruct H1 as [n N].
  exists (S n), c', m'; eexists; eexists; split. eassumption.
  split. eassumption. trivial.
+ constructor; trivial. destruct H1 as [n N].
  exists (S n), c', m'; eexists; eexists; split. eassumption.
  split. eassumption. trivial.
+ constructor; intros. destruct n. 
  - eexists; eexists; reflexivity. 
  - simpl. destruct (H1 n) as [cc [mm CM]].
    apply effstep_corestep in H.
    exists cc, mm, c', m'. split; trivial.
Qed. 

Definition minuseffect {C} m (U:block -> Z -> bool) (R: @MidStepEffectResult C) :=
  match R with
    MSE_Ext c' m' W f args => MSE_Ext c' m' (fun b z => W b z && valid_block_dec m b)  f args
  | MSE_Ret c' m' W v => MSE_Ret c' m' (fun b z => U b z || W b z  && valid_block_dec m b) v
  | MSE_Div => MSE_Div
  end.

Lemma midtepE_preserves_effstep {G C} (SEM : @EffectSem G C) g
   (DET: forall c m c1 m1 U1 c2 m2 U2, effstep SEM g U1 c m c1 m1 -> 
         effstep SEM g U2 c m c2 m2 -> (c1,m1,U1)=(c2,m2,U2)):
   forall c m U c' m', effstep SEM g U c m c' m' ->
   forall R, midstepE SEM g c m R -> 
          midstepE SEM g c' m' (minuseffect 
Proof. intros. destruct R. simpl.
+ rename b into V. simpl in H0. inv H0. constructor; trivial. 
  remember (fun (b : block) (z : Z) => U b z || V b z && valid_block_dec m b) as W.
  generalize dependent V. 
  destruct H3 as [n N]. generalize dependent W. 
  destruct n; simpl in *; intros.
  - destruct N as [N1 N2]. inv N1.
    apply effstep_corestep in H.
    apply corestep_not_at_external in H. congruence.
  - destruct N as [cc [mm [U1 [U2 [STEP [STEPS HU]]]]]].
    specialize (DET _ _ _ _ _ _ _ _ H STEP); inv DET.
    exists n; trivial.
+ constructor; trivial.
  destruct H1 as [n N].
  induction n; simpl in *.
  - inv N. apply corestep_not_halted in H. congruence.
  - destruct N as [cc [mm [STEP STEPS]]]. specialize (DET _ _ _ _ _ _ H STEP); inv DET.
    exists n; trivial.
+ constructor; intros. destruct (H1 (S n)) as [cc [mm MM]]; clear H1; simpl in MM.
  destruct MM as [c1 [m1 [STEP STEPS]]].
  specialize (DET _ _ _ _ _ _ H STEP); inv DET.
  exists cc, mm; trivial.
Qed.

Definition addeffect {C} m (U:block -> Z -> bool) (R: @MidStepEffectResult C) :=
  match R with
    MSE_Ext c' m' W f args => MSE_Ext c' m' (fun b z => U b z || W b z  && valid_block_dec m b)  f args
  | MSE_Ret c' m' W v => MSE_Ret c' m' (fun b z => U b z || W b z  && valid_block_dec m b) v
  | MSE_Div => MSE_Div
  end.

Lemma midtepE_preserves_effstep_rev {G C} (SEM : @EffectSem G C) g:
   forall c m  U c' m', effstep SEM g U c m c' m' ->
   forall R, midstepE SEM g c' m' R -> midstepE SEM g c m (addeffect m U R).
Proof. intros. inv H0.
+ constructor; trivial. destruct H1 as [n N].
  exists (S n), c', m'; eexists; eexists; split. eassumption.
  split. eassumption. trivial.
+ constructor; trivial. destruct H1 as [n N].
  exists (S n), c', m'; eexists; eexists; split. eassumption.
  split. eassumption. trivial.
+ constructor; intros. destruct n. 
  - eexists; eexists; reflexivity. 
  - simpl. destruct (H1 n) as [cc [mm CM]].
    apply effstep_corestep in H.
    exists cc, mm, c', m'. split; trivial.
Qed. 

Lemma midtepE_preserves_effstep {G C} (SEM : @EffectSem G C) g
   (DET: forall c m c1 m1 U1 c2 m2 U2, effstep SEM g U1 c m c1 m1 -> 
         effstep SEM g U2 c m c2 m2 -> (c1,m1,U1)=(c2,m2,U2)):
   forall c m U c' m', effstep SEM g U c m c' m' ->
   forall R, midstepE SEM g c m (addeffect m U R) -> 
          midstepE SEM g c' m' R.
Proof. intros. destruct R. simpl.
+ rename b into V.  simpl in H0. inv H0. constructor; trivial. 
  remember (fun (b : block) (z : Z) => U b z || V b z && valid_block_dec m b) as W.
  generalize dependent V. 
  destruct H3 as [n N]. generalize dependent W. 
  destruct n; simpl in *; intros.
  - destruct N as [N1 N2]. inv N1.
    apply effstep_corestep in H.
    apply corestep_not_at_external in H. congruence.
  - destruct N as [cc [mm [U1 [U2 [STEP [STEPS HU]]]]]].
    specialize (DET _ _ _ _ _ _ _ _ H STEP); inv DET.
    exists n; trivial.
+ constructor; trivial.
  destruct H1 as [n N].
  induction n; simpl in *.
  - inv N. apply corestep_not_halted in H. congruence.
  - destruct N as [cc [mm [STEP STEPS]]]. specialize (DET _ _ _ _ _ _ H STEP); inv DET.
    exists n; trivial.
+ constructor; intros. destruct (H1 (S n)) as [cc [mm MM]]; clear H1; simpl in MM.
  destruct MM as [c1 [m1 [STEP STEPS]]].
  specialize (DET _ _ _ _ _ _ H STEP); inv DET.
  exists cc, mm; trivial.
Qed.
*)