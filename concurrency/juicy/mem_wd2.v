(* A stronger version of mem_wd2. Adapted from sepcomp/mem_wd2.v. *)
Require Import compcert.lib.Integers.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.common.AST.
Require Import compcert.common.Values.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import VST.sepcomp.mem_lemmas.
Require Import VST.sepcomp.mem_wd.
Require Import VST.concurrency.juicy.semax_simlemmas.
Require Import VST.msl.eq_dec.

Definition mem_wd2 m := forall b ofs, memval_inject (Mem.flat_inj (Mem.nextblock m))
    (ZMap.get ofs (PMap.get b (Mem.mem_contents m))) (ZMap.get ofs (PMap.get b (Mem.mem_contents m))).

Lemma mem_wd2_alloc: forall m b lo hi m' (ALL: Mem.alloc m lo hi = (m',b))
     (WDm: mem_wd2 m), mem_wd2 m'.
Proof.
  unfold mem_wd2; intros.
  erewrite Mem.nextblock_alloc by eauto.
  destruct (eq_dec b0 b); [subst; erewrite AllocContentsUndef by eauto | erewrite AllocContentsOther by eauto].
  - rewrite ZMap.gi; constructor.
  - eapply memval_inject_incr, flat_inj_incr, Ple_succ; auto.
Qed.

Lemma mem_wd2_store: forall m b ofs v m' chunk (WDm: mem_wd2 m)
  (ST: Mem.store chunk m b ofs v = Some m')
  (V: val_valid v m), mem_wd2 m'.
Proof.
  unfold mem_wd2; intros.
  rewrite (Mem.nextblock_store _ _ _ _ _ _ ST).
  erewrite Mem.store_mem_contents by eauto.
  destruct (eq_dec b0 b); [subst; rewrite PMap.gss | rewrite PMap.gso; auto].
  replace ofs0 with (ofs0 + 0) at 2 by apply Z.add_0_r.
  replace ofs with (ofs + 0) at 2 by apply Z.add_0_r.
  apply Mem.setN_inj with (access := fun _ => True); intros; rewrite ?Z.add_0_r; auto.
  apply encode_val_inject.
  destruct v; try solve [constructor].
  econstructor; [|symmetry; apply Ptrofs.add_zero].
  eapply flatinj_I; auto.
Qed.

Import FunInd.

Lemma mem_wd2_store_zeros: forall m b p n m1
    (STORE_ZERO: store_zeros m b p n = Some m1) (WD: mem_wd2 m), mem_wd2 m1.
Proof. intros until n. functional induction (store_zeros m b p n); intros.
  inv STORE_ZERO; tauto.
  apply (IHo _ STORE_ZERO); clear IHo.
      eapply (mem_wd2_store m). apply WD. apply e0. simpl; trivial.
  inv STORE_ZERO.
Qed.

Lemma mem_wd2_store_init_data: forall {F V} (ge: Genv.t F V) a (b:block) (z:Z)
  m1 m2 (SID:Genv.store_init_data ge m1 b z a = Some m2),
  valid_genv ge m1 -> mem_wd2 m1 -> mem_wd2 m2.
Proof. intros F V ge a.
  destruct a; simpl; intros;
      try apply (mem_wd2_store _ _ _ _ _ _ H0 SID); simpl; trivial.
   inv SID; trivial.
   remember (Genv.find_symbol ge i) as d.
     destruct d; inv SID.
     eapply (mem_wd2_store _ _ _ _ _ _ H0 H2).
    apply eq_sym in Heqd.
    destruct H.
    apply v.
    unfold isGlobalBlock.
    rewrite orb_true_iff.
    unfold genv2blocksBool; simpl.
    apply Genv.find_invert_symbol in Heqd.
    rewrite Heqd; left; auto.
Qed.

Lemma valid_genv_store_init_data:
  forall {F V}  (ge: Genv.t F V) a (b:block) (z:Z) m1 m2
  (SID: Genv.store_init_data ge m1 b z a = Some m2),
  valid_genv ge m1 -> valid_genv ge m2.
Proof. intros F V ge a.
  destruct a; simpl; intros; inv H; constructor;
    try (intros b0 X; eapply Mem.store_valid_block_1 with (b':=b0); eauto;
          apply H0; auto);
    try (intros b0 ? X; eapply Mem.store_valid_block_1 with (b':=b0); eauto;
          eapply H1; eauto);
    try (inv SID; auto).
  intros.
  remember (Genv.find_symbol ge i) as d.
  destruct d; inv H2.
  eapply Mem.store_valid_block_1; eauto.
  apply eq_sym in Heqd.
  eapply H0; eauto.
  revert H2. destruct (Genv.find_symbol ge i); intros; try congruence.
  eapply Mem.store_valid_block_1; eauto.
  eapply H1; eauto.
Qed.

Lemma mem_wd2_store_init_datalist: forall {F V} (ge: Genv.t F V) l (b:block)
  (z:Z) m1 m2 (SID: Genv.store_init_data_list ge m1 b z l = Some m2),
  valid_genv ge m1 -> mem_wd2 m1 -> mem_wd2 m2.
Proof. intros F V ge l.
  induction l; simpl; intros.
    inv SID. trivial.
  remember (Genv.store_init_data ge m1 b z a) as d.
  destruct d; inv SID; apply eq_sym in Heqd.
  apply (IHl _ _ _ _ H2); clear IHl H2.
     eapply valid_genv_store_init_data. apply Heqd. apply H.
  eapply mem_wd2_store_init_data. apply Heqd. apply H. apply H0.
Qed.

Lemma valid_genv_store_init_datalist: forall {F V} (ge: Genv.t F V) l (b:block)
  (z:Z) m1 m2 (SID: Genv.store_init_data_list ge m1 b z l = Some m2),
   valid_genv ge m1 -> valid_genv ge m2.
Proof. intros F V ge l.
  induction l; simpl; intros.
    inv SID. trivial.
  remember (Genv.store_init_data ge m1 b z a) as d.
  destruct d; inv SID; apply eq_sym in Heqd.
  apply (IHl _ _ _ _ H1); clear IHl H1.
     eapply valid_genv_store_init_data. apply Heqd. apply H.
Qed.

Lemma mem_wd2_drop: forall m b lo hi p m' (DROP: Mem.drop_perm m b lo hi p = Some m')
     (WDm: mem_wd2 m), Mem.valid_block m b -> mem_wd2 m'.
Proof.
  unfold mem_wd2; intros.
  unfold Mem.drop_perm in DROP.
  destruct (Mem.range_perm_dec _ _ _ _ _ _); inv DROP; auto.
Qed.

Lemma mem_wd2_alloc_global: forall  {F V} (ge: Genv.t F V) a m0 m1
   (GA: Genv.alloc_global ge m0 a = Some m1),
   mem_wd2 m0 -> valid_genv ge m0 -> mem_wd2 m1.
Proof. intros F V ge a.
destruct a; simpl. intros.
destruct g.
  remember (Mem.alloc m0 0 1) as mm. destruct mm.
    apply eq_sym in Heqmm.
    specialize (mem_wd2_alloc _ _ _ _ _ Heqmm). intros.
     eapply (mem_wd2_drop _ _ _ _ _  _ GA).
    apply (H1 H).
    apply (Mem.valid_new_block _ _ _ _ _ Heqmm).
remember (Mem.alloc m0 0 (init_data_list_size (AST.gvar_init v)) ) as mm.
  destruct mm. apply eq_sym in Heqmm.
  remember (store_zeros m b 0 (init_data_list_size (AST.gvar_init v)))
           as d.
  destruct d; inv GA; apply eq_sym in Heqd.
  remember (Genv.store_init_data_list ge m2 b 0 (AST.gvar_init v)) as dd.
  destruct dd; inv H2; apply eq_sym in Heqdd.
  eapply (mem_wd2_drop _ _ _ _ _ _ H3); clear H3.
    eapply (mem_wd2_store_init_datalist _ _ _ _ _ _ Heqdd).
    apply (valid_genv_store_zeros _ _ _ _ _ _ Heqd).
    apply (valid_genv_alloc ge _ _ _ _ _ Heqmm H0).
  apply (mem_wd2_store_zeros _ _ _ _ _ Heqd).
    apply (mem_wd2_alloc _ _ _ _ _ Heqmm H).
  unfold Mem.valid_block.
     apply Genv.store_init_data_list_nextblock in Heqdd.
           rewrite Heqdd. clear Heqdd.
      apply Genv.store_zeros_nextblock in Heqd. rewrite Heqd; clear Heqd.
      apply (Mem.valid_new_block _ _ _ _ _  Heqmm).
Qed.

Lemma valid_genv_alloc_global: forall  {F V} (ge: Genv.t F V) a m0 m1
   (GA: Genv.alloc_global ge m0 a = Some m1),
   valid_genv ge m0 -> valid_genv ge m1.
Proof. intros F V ge a.
destruct a; simpl. intros.
destruct g.
  remember (Mem.alloc m0 0 1) as d. destruct d.
    apply eq_sym in Heqd.
    apply (valid_genv_drop _ _ _ _ _ _ _ GA).
    apply (valid_genv_alloc _ _ _ _ _ _ Heqd H).
remember (Mem.alloc m0 0 (init_data_list_size (AST.gvar_init v)) )
         as Alloc.
  destruct Alloc. apply eq_sym in HeqAlloc.
  remember (store_zeros m b 0
           (init_data_list_size (AST.gvar_init v))) as SZ.
  destruct SZ; inv GA; apply eq_sym in HeqSZ.
  remember (Genv.store_init_data_list ge m2 b 0 (AST.gvar_init v)) as Drop.
  destruct Drop; inv H1; apply eq_sym in HeqDrop.
  eapply (valid_genv_drop _ _ _ _ _ _ _ H2); clear H2.
  eapply (valid_genv_store_init_datalist _ _ _ _ _ _ HeqDrop). clear HeqDrop.
  apply (valid_genv_store_zeros _ _ _ _ _ _ HeqSZ).
    apply (valid_genv_alloc _ _ _ _ _ _ HeqAlloc H).
Qed.

Lemma valid_genv_alloc_globals:
   forall F V (ge: Genv.t F V) init_list m0 m
   (GA: Genv.alloc_globals ge m0 init_list = Some m),
   valid_genv ge m0 -> valid_genv ge m.
Proof. intros F V ge l.
induction l; intros; simpl in *.
  inv GA. assumption.
remember (Genv.alloc_global ge m0 a) as d.
  destruct d; inv GA. apply eq_sym in Heqd.
  eapply (IHl  _ _  H1). clear H1.
    apply (valid_genv_alloc_global _ _ _ _ Heqd H).
Qed.

Lemma mem_wd2_alloc_globals:
   forall F V (ge: Genv.t F V) init_list m0 m
   (GA: Genv.alloc_globals ge m0 init_list = Some m),
   mem_wd2 m0 -> valid_genv ge m0 -> mem_wd2 m.
Proof. intros F V ge l.
induction l; intros; simpl in *.
  inv GA. assumption.
remember (Genv.alloc_global ge m0 a) as d.
  destruct d; inv GA. apply eq_sym in Heqd.
eapply (IHl  _ _  H2).
    apply (mem_wd2_alloc_global ge _ _ _ Heqd H H0).
    apply (valid_genv_alloc_global _ _ _ _ Heqd H0).
Qed.
