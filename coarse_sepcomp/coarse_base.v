Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.lib.Integers.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Events.
Require Import VST.msl.Axioms.
Require Import VST.coarse_sepcomp.coarse_defs.
(*
(*From mem_lemmas*)
Notation val_inject:= Val.inject.

Definition mem_forward (m1 m2:mem) :=
  forall b (B:Mem.valid_block m1 b),
    Mem.valid_block m2 b
    /\ (forall ofs p, Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p).

Definition LocsetB:Type := block -> Z -> bool.
Definition Locset:Type := block -> Z -> Prop.

(** * Simulations *)
Definition Blockset:Type := block -> bool.

(*Require Import VST.sepcomp.mem_lemmas.*)
Lemma valid_block_dec: forall m b, {Mem.valid_block m b} +  {~Mem.valid_block m b}.
Proof. intros.
unfold Mem.valid_block.
remember (plt b (Mem.nextblock m)).
destruct s. left; assumption.
right. intros N. xomega.
Qed.

Definition freshblockB m m' b:bool := valid_block_dec m' b && negb (valid_block_dec m b).
Definition freshblock m m' b:Prop := Mem.valid_block m' b /\ ~ Mem.valid_block m b.

(*If SRC-writes are confined to X, TGT-writes are confined to locations in the j-image of X and local blocks*)
Definition write_confined m1 m1' (j:meminj) (LT:Blockset) m2 m2':Prop :=
   forall (X:Locset) (HX: forall b z (Hb1: Mem.valid_block m1 b), 
                          Mem.unchanged_on (fun b' z' => (b',z')=(b,z)) m1 m1' \/ X b z)
          b2 z (Hz: Mem.valid_block m2 b2), 
   Mem.unchanged_on (fun bb zz => (bb,zz)=(b2,z)) m2 m2' \/
   LT b2 = true (*could probably be strengthened to LT b2 - true /\ loc_out_of_reach j m1' b2 z*) \/
   (exists b1 d, j b1 = Some(b2,d) /\ X b1 (z-d)).

(*If SRC-writes are confined to X, TGT-writes are confined to locations in X and local blocks*)
Definition write_confinedExt m1 m1' (L:Blockset) m2 m2':Prop :=
   forall (X:Locset) (HX: forall b z (Hb1: Mem.valid_block m1 b), 
                          Mem.unchanged_on (fun b' z' => (b',z')=(b,z)) m1 m1' \/ X b z)
          b2 z (Hz: Mem.valid_block m2 b2), 
   Mem.unchanged_on (fun bb zz => (bb,zz)=(b2,z)) m2 m2' \/ L b2 = true \/ X b2 z.

(*
Definition lsep m (j j':meminj) := forall b1 b2 d, j b1 = None -> 
   j' b1 = Some (b2,d) -> ~Mem.valid_block m b1.*)
Definition isep m1 (j j':meminj) m2 (LT:Blockset) := forall b1 b2 d 
           (J:j b1 = None) (J':j' b1 = Some (b2,d)),
           ~Mem.valid_block m1 b1 /\ (Mem.valid_block m2 b2 -> LT b2 = true).
Definition esep m1 (j j':meminj) m2 (LT:Blockset) := forall b1 b2 d 
           (J:j b1 = None) (J':j' b1 = Some (b2,d)),
           ~Mem.valid_block m1 b1 /\ (Mem.valid_block m2 b2 -> LT b2 = false).

Definition full_comp (j1 j2: meminj) :=
  forall b0 b1 delta1, j1 b0 = Some (b1, delta1) -> exists b2 delta2, j2 b1 = Some (b2, delta2).

Definition genv2blocksBool {F V : Type} (ge : Genv.t F V):=
  (fun b =>
      match Genv.invert_symbol ge b with
        Some id => true
      | None => false
      end,
   fun b => match Genv.find_var_info ge b with
                  Some gv => true
                | None => false
            end).

Definition isGlobalBlock {F V : Type} (ge : Genv.t F V) :=
  fun b => (fst (genv2blocksBool ge)) b || (snd (genv2blocksBool ge)) b.

Definition globals_separate {F V:Type} (ge: Genv.t F V) (j j': meminj) :=
    forall b1 b2 d, j b1 = None -> j' b1 =Some(b2,d) ->
           isGlobalBlock ge b2 = false.

Definition globals_preserved {F1 V1 F2 V2:Type} (ge1: Genv.t F1 V1) (ge2: Genv.t F2 V2) (j:meminj) :=
 forall b1 b2 d, j b1 = Some(b2,d) -> isGlobalBlock ge1 b1 = isGlobalBlock ge2 b2.

Definition globals_valid {F V:Type} (ge: Genv.t F V) (m:mem):=
 forall b, isGlobalBlock ge b = true -> Mem.valid_block m b.

Definition ReadOnlyBlocks {F V} (ge: Genv.t F V) (b:block): bool :=
  match Genv.find_var_info ge b with
          None => false
        | Some gv => gvar_readonly gv && negb (gvar_volatile gv)
  end.

Definition readonly m1 b m2 :=
    forall n ofs (NWR: forall i, 0 <= i < n -> ~(Mem.perm m1 b (ofs + i) Cur Writable)),
     Mem.loadbytes m2 b ofs n = Mem.loadbytes m1 b ofs n /\
     (forall i, 0 <= i < n -> (forall k p, Mem.perm m1 b (ofs+i) k p <-> Mem.perm m2 b (ofs+i) k p)).

Definition RDOnly_fwd (m1 m1':mem) B :=
  forall b (Hb: B b = true), readonly m1 b m1'.

Definition mem_respects_readonly {F V} (ge : Genv.t F V) m :=
    forall b gv, Genv.find_var_info ge b = Some gv ->
                 gvar_readonly gv && negb (gvar_volatile gv) = true ->
           Genv.load_store_init_data ge m b 0 (gvar_init gv) /\
           Mem.valid_block m b /\ (forall ofs : Z, ~ Mem.perm m b ofs Max Writable).

Definition forward {F V:Type} (ge:Genv.t F V) m1 m2 := mem_forward m1 m2
    /\ RDOnly_fwd m1 m2 (ReadOnlyBlocks ge).


Definition full_ext  (LS: Blockset) (j1 j2: meminj):=
  forall b1 b2 delta1, j1 b1 = Some (b2, delta1) -> LS b1 = false ->
  exists b3 delta2, j2 b2 = Some (b3, delta2).
*) 

Lemma mem_forward_nextblock:
  forall m m', mem_forward m m' -> Ple  (Mem.nextblock m) (Mem.nextblock m').
Proof.
intros. hnf in H.
unfold Mem.valid_block in H.
pose proof (Ppred_Plt (Mem.nextblock m)).
unfold Ple, Plt in *.
destruct (peq (Mem.nextblock m) 1).
rewrite e. apply Pos.le_1_l.
specialize (H0 n).
destruct (H _ H0) as [? _]; clear H.
pose proof (Pos.succ_pred _ n).
rewrite <- H; apply Pos.le_succ_l; auto.
Qed.

Lemma compose_meminjD_None j1 j2 b1 (J: compose_meminj j1 j2 b1 = None):
  j1 b1 = None \/ exists b2 d1, j1 b1= Some(b2,d1) /\ j2 b2=None.
Proof. unfold compose_meminj in J.
  destruct (j1 b1); [destruct p as [b2 d1]; right | left; trivial ].
  exists b2, d1.
  destruct (j2 b2); [ destruct p; congruence | split; trivial].
Qed. 

Lemma compose_meminjD_Some j1 j2 b1 b3 d (J: compose_meminj j1 j2 b1 = Some(b3,d)):
  exists b2 d1 d2, j1 b1= Some(b2,d1) /\ j2 b2=Some(b3,d2) /\ d=d1+d2.
Proof. unfold compose_meminj in J.
  destruct (j1 b1); [destruct p as [b2 d1] | congruence].
  exists b2, d1.
  destruct (j2 b2); [destruct p as [? d2] | congruence].
  inv J. exists d2; repeat split; trivial. 
Qed. 

Lemma inject_incr_compose_meminj j1 j2 j1' j2' (I1: inject_incr j1 j1') (I2: inject_incr j2 j2'):
      inject_incr (compose_meminj j1 j2) (compose_meminj j1' j2').
Proof. red; intros b1 b3 d J.
  apply compose_meminjD_Some in J. destruct J as [b2 [d1 [d2 [J1 [J2 D]]]]].
  unfold compose_meminj. rewrite (I1 _ _ _ J1), (I2 _ _ _ J2); subst; trivial.
Qed.

Lemma Forall2_val_inject_compose j1 j2: forall vals1 vals2
  (ArgsInj12 : Forall2 (val_inject j1) vals1 vals2) vals3
  (ArgsInj23 : Forall2 (val_inject j2) vals2 vals3),
  Forall2 (val_inject (compose_meminj j1 j2)) vals1 vals3.
Proof.
induction vals1; intros.
+ inv ArgsInj12; inv ArgsInj23. constructor.
+ inv ArgsInj12; inv ArgsInj23. constructor. eapply val_inject_compose; eauto. eauto.
Qed.

Lemma forward_unchanged_on: forall m m' (FWD: mem_forward m m')
           b ofs (NP: ~ Mem.perm m b ofs Max Nonempty),
     Mem.unchanged_on (fun b' ofs' => b' = b /\ ofs' = ofs) m m'.
Proof. intros.
split; intros.
  apply mem_forward_nextblock; auto.
  destruct H; subst.
  split; intros; elim NP.
    eapply Mem.perm_max.
    eapply Mem.perm_implies; try eassumption. apply perm_any_N.
    destruct (FWD _ H0) as [VB' P]. eapply Mem.perm_implies.
       apply P. eapply Mem.perm_max; eassumption. apply perm_any_N.
destruct H; subst.
  elim NP. eapply Mem.perm_max.
  eapply Mem.perm_implies; try eassumption. apply perm_any_N.
Qed.


(*This is the motivating lemma for the definition of write_confined - it is
the mirrored (in the sense of L b = true versus false) version of the
unchanged_on assumption made by external calls*)
Lemma confined_unch_loor m1 m1' j LT m2 m2' (FWD1: mem_forward m1 m1') (FWD2: mem_forward m2 m2')
   (C: write_confined m1 m1' j LT m2 m2'):
   Mem.unchanged_on (fun b z => LT b = false /\ loc_out_of_reach j m1 b z) m2 m2'.
Proof.
assert(HX: forall b z, Mem.valid_block m1 b ->
     Mem.unchanged_on (fun b' z' => (b', z') = (b, z)) m1 m1' \/ (fun b z => Mem.perm m1 b z Max Nonempty) b z).
  { intros bb z BB. destruct (Mem.perm_dec m1 bb z Max Nonempty). right; trivial. left.
    eapply Mem.unchanged_on_implies. apply (forward_unchanged_on _ _ FWD1 _ _ n). simpl; intros. inv H; split; trivial. } 
split. 
+ apply mem_forward_nextblock; trivial.
+ intros. destruct H.
  destruct (C _ HX _ ofs H0) as [K | [K | K]]; clear HX C.
  - apply K; trivial. 
  - congruence. 
  - destruct K as [bb [d [J ?]]]. elim (H1 _ _ J); trivial.
+ intros. destruct H.
  specialize (Mem.perm_valid_block _ _ _ _ _ H0); intros.
  destruct (C _ HX _ ofs H2) as [K | [K | K]]; clear HX C.
  - apply K; trivial. 
  - congruence. 
  - destruct K as [bb [d [J ?]]]. elim (H1 _ _ J); trivial.
Qed.

Lemma find_var_info_isGlobal: forall {V F} (ge : Genv.t F V) b x,
      Genv.find_var_info ge b = Some x -> isGlobalBlock ge b = true.
Proof. intros.
  unfold isGlobalBlock, genv2blocksBool. simpl.
  rewrite H, orb_true_r; trivial.
Qed.

Lemma ReadOnlyBlocks_global {F V} (g:Genv.t F V) b:
      ReadOnlyBlocks g b = true -> isGlobalBlock g b = true.
Proof.
   unfold ReadOnlyBlocks; intros.
   remember (Genv.find_var_info g b) as d. destruct d; try discriminate.
   eapply find_var_info_isGlobal. rewrite <- Heqd; reflexivity.
Qed.

Lemma readonly_refl m b: readonly m b m.
  Proof. red; intuition. Qed.

Lemma readonly_trans m1 m2 m3 b: readonly m1 b m2 -> readonly m2 b m3 -> readonly m1 b m3.
  Proof. red; intros. destruct (H _ _ NWR); clear H.
    destruct (H0 n ofs); clear H0.
      intros. intros N. apply (NWR _ H). apply (H2 _ H). assumption.
    split. rewrite <- H1. assumption.
    intros. destruct (H2 _ H0 k p); clear H2. destruct (H3 _ H0 k p); clear H3.
      split; eauto.
  Qed.

Lemma RDOnly_fwd_refl m B : RDOnly_fwd m m B.
Proof. split; trivial. intros; split; trivial. Qed.

Lemma RDOnly_fwd_trans m1 m2 m3 B:
  RDOnly_fwd m1 m2 B -> RDOnly_fwd m2 m3 B -> RDOnly_fwd m1 m3 B.
Proof. intros; red; intros.
  eapply readonly_trans. apply H; eauto. apply H0; eauto.
Qed.

Definition readonlyLD m1 b m2 :=
    forall chunk ofs
    (NWR: forall ofs', ofs <= ofs' < ofs + size_chunk chunk ->
                          ~(Mem.perm m1 b ofs' Cur Writable)),
     Mem.load chunk m2 b ofs = Mem.load chunk m1 b ofs /\
     (forall ofs', ofs <= ofs' < ofs + size_chunk chunk ->
        (forall k p, Mem.perm m1 b ofs' k p <-> Mem.perm m2 b ofs' k p)).

Lemma readonly_readonlyLD m1 b m2: readonly m1 b m2 -> readonlyLD m1 b m2.
Proof.
  red; intros. destruct (H (size_chunk chunk) ofs); clear H.
    intros. apply NWR. omega.
  split; intros.
    remember (Mem.load chunk m2 b ofs) as d; symmetry in Heqd; symmetry.
    destruct d.
    { destruct (Mem.load_loadbytes _ _ _ _ _ Heqd) as [bytes [LDB V]]; subst v.
      apply Mem.load_valid_access in Heqd; destruct Heqd.
      rewrite H0 in LDB. apply Mem.loadbytes_load; trivial.
    }
    { remember (Mem.load chunk m1 b ofs) as q; symmetry in Heqq; symmetry.
      destruct q; trivial.
      destruct (Mem.load_loadbytes _ _ _ _ _ Heqq) as [bytes [LDB V]]; subst v.
      apply Mem.load_valid_access in Heqq; destruct Heqq.
      rewrite <- Heqd.
      rewrite <- H0 in LDB. apply Mem.loadbytes_load; trivial. }
  specialize (H1 (ofs'-ofs)). rewrite Zplus_minus in H1. apply H1. omega.
Qed.

(*
Definition readonly' {F V} (ge : Genv.t F V) m1 b m2 :=
    Mem.unchanged_on (fun b' z => b'=b /\ ReadOnlyBlocks ge b' = true) m1 m2.

Lemma readonly_readonly' {F V} (ge : Genv.t F V) b m1 m2: mem_forward m1 m2 -> mem_respects_readonly ge m1 -> readonly m1 b m2 -> readonly' ge m1 b m2.
Proof. intros. 
  assert (P: forall ofs k p, ReadOnlyBlocks ge b = true -> Mem.valid_block m1 b -> Mem.perm m1 b ofs k p <-> Mem.perm m2 b ofs k p).
  { intros. destruct (H1 1 ofs).
    - intros. intros N. unfold ReadOnlyBlocks in H2. specialize (H0 b).
      destruct (Genv.find_var_info ge b); try discriminate.
      destruct (H0 g) as [_ [? ?]]; trivial.
      apply (H6 ofs). assert (i=0) by omega. subst i. rewrite Zplus_0_r in N. eapply Mem.perm_max. eassumption.
    - specialize (H5 0). rewrite Zplus_0_r in H5. apply H5; omega. } 
  split.
  + apply mem_forward_nextblock; trivial.
  + intros. destruct H2; subst. auto. 
  + intros. destruct H2; subst. specialize (P ofs Cur Readable H4). destruct (H1 1 ofs).
    - intros. intros N. unfold ReadOnlyBlocks in H4. specialize (H0 b).
      destruct (Genv.find_var_info ge b); try discriminate.
      destruct (H0 g) as [_ [? ?]]; trivial.
      apply (H6 ofs). assert (i=0) by omega. subst i. rewrite Zplus_0_r in N. eapply Mem.perm_max. eassumption.
    - Transparent Mem.loadbytes.  unfold Mem.loadbytes in H2. Opaque Mem.loadbytes.
      simpl in H2. destruct (Mem.range_perm_dec m1 b ofs (ofs + 1) Cur Readable).
      * destruct (Mem.range_perm_dec m2 b ofs (ofs + 1) Cur Readable).
        ++ inv H2; trivial.
        ++ elim n; clear n. red; intros. assert (ofs0 = ofs) by omega; subst. apply P; trivial. eapply Mem.perm_valid_block. eapply H3.
      * elim n; clear n. red; intros. assert (ofs0=ofs) by omega; subst; trivial.
Qed.
*)

Lemma mem_respects_readonly_fwd {F V} (g : Genv.t F V) m m'
         (MRR: mem_respects_readonly g m)
         (FWD: mem_forward m m')
         (RDO: forall b, Mem.valid_block m b -> readonly m b m'):
         mem_respects_readonly g m'.
Proof. red; intros. destruct (MRR _ _ H H0) as [LSI [VB NP]]; clear MRR.
destruct (FWD _ VB) as [VB' Perm].
split. eapply Genv.load_store_init_data_invariant; try eassumption.
       intros. eapply readonly_readonlyLD. eapply RDO; try eassumption.
       intros. intros N. apply (NP ofs'). eapply Mem.perm_max; eassumption. (* apply NP.*)
split. trivial.
intros z N. apply (NP z); eauto.
Qed.

Lemma mem_respects_readonly_forward {F V} (ge : Genv.t F V) m m'
         (MRR: mem_respects_readonly ge m)
         (FWD: mem_forward m m')
         (RDO: forall b gv, Genv.find_var_info ge b = Some gv ->
                 gvar_readonly gv && negb (gvar_volatile gv) = true -> readonly m b m'):
         mem_respects_readonly ge m'.
Proof. red; intros. destruct (MRR _ _ H H0) as [LSI [VB NP]]; clear MRR.
destruct (FWD _ VB) as [VB' Perm].
split. eapply Genv.load_store_init_data_invariant; try eassumption.
       intros. eapply readonly_readonlyLD. eapply RDO; try eassumption.
       intros. intros N. apply (NP ofs'). eapply Mem.perm_max; eassumption. (* apply NP.*)
split. trivial.
intros z N. apply (NP z); eauto.
Qed.

Lemma mem_respects_readonly_forward' {F V} (ge : Genv.t F V) m m'
         (MRR: mem_respects_readonly ge m)
         (FWD: mem_forward m m')
         (RDO: RDOnly_fwd m m' (ReadOnlyBlocks ge)):
         mem_respects_readonly ge m'.
Proof. red; intros. destruct (MRR _ _ H H0) as [LSI [VB NP]]; clear MRR.
destruct (FWD _ VB) as [VB' Perm].
split. eapply Genv.load_store_init_data_invariant; try eassumption.
       intros. eapply readonly_readonlyLD. eapply RDO; try eassumption. unfold ReadOnlyBlocks. rewrite H; trivial.
       intros. intros N. apply (NP ofs'). eapply Mem.perm_max; eassumption. (* apply NP.*)
split. trivial.
intros z N. apply (NP z); eauto.
Qed.

Lemma load_storebytes_nil m b ofs m': Mem.storebytes m b ofs nil = Some m' ->
  forall ch bb z, Mem.load ch m' bb z = Mem.load ch m bb z.
Proof. intros.
  remember (Mem.load ch m' bb z) as u'; symmetry in Hequ'; destruct u'.
      symmetry.
      eapply Mem.load_unchanged_on; try eassumption.
      instantiate (1:= fun b ofs => True).
      split; intros.
        rewrite (Mem.nextblock_storebytes _ _ _ _ _ H); apply Ple_refl.
        split; intros.
          eapply Mem.perm_storebytes_2; eassumption.
          eapply Mem.perm_storebytes_1; eassumption.
      rewrite (Mem.storebytes_mem_contents _ _ _ _ _ H).
      destruct (eq_block b0 b); subst. rewrite PMap.gss; trivial.
      rewrite PMap.gso; trivial.
    intros; simpl; trivial.

    remember (Mem.load ch m bb z) as u; symmetry in Hequ; destruct u; trivial.
      rewrite <- Hequ'; clear Hequ'.
      eapply Mem.load_unchanged_on; try eassumption.
      instantiate (1:= fun b ofs => True).
      split; intros.
        rewrite (Mem.nextblock_storebytes _ _ _ _ _ H); apply Ple_refl.
        split; intros.
          eapply Mem.perm_storebytes_1; eassumption.
          eapply Mem.perm_storebytes_2; eassumption.
      rewrite (Mem.storebytes_mem_contents _ _ _ _ _ H).
      destruct (eq_block b0 b); subst. rewrite PMap.gss; trivial.
      rewrite PMap.gso; trivial.
    intros; simpl; trivial.
Qed.

Lemma loadbytes_storebytes_nil m b ofs m': Mem.storebytes m b ofs nil = Some m' ->
  forall n bb z, Mem.loadbytes m' bb z n = Mem.loadbytes m bb z n.
Proof. intros.
  remember (Mem.loadbytes m' bb z n) as u'; symmetry in Hequ'; destruct u'.
      symmetry.
      eapply Mem.loadbytes_unchanged_on; try eassumption.
      instantiate (1:= fun b ofs => True).
      split; intros.
        rewrite (Mem.nextblock_storebytes _ _ _ _ _ H); apply Ple_refl.
        split; intros.
          eapply Mem.perm_storebytes_2; eassumption.
          eapply Mem.perm_storebytes_1; eassumption.
      rewrite (Mem.storebytes_mem_contents _ _ _ _ _ H).
      destruct (eq_block b0 b); subst. rewrite PMap.gss; trivial.
      rewrite PMap.gso; trivial.
    intros; simpl; trivial.

    remember (Mem.loadbytes m bb z n) as u; symmetry in Hequ; destruct u; trivial.
      rewrite <- Hequ'; clear Hequ'.
      eapply Mem.loadbytes_unchanged_on; try eassumption.
      instantiate (1:= fun b ofs => True).
      split; intros.
        rewrite (Mem.nextblock_storebytes _ _ _ _ _ H); apply Ple_refl.
        split; intros.
          eapply Mem.perm_storebytes_1; eassumption.
          eapply Mem.perm_storebytes_2; eassumption.
      rewrite (Mem.storebytes_mem_contents _ _ _ _ _ H).
      destruct (eq_block b0 b); subst. rewrite PMap.gss; trivial.
      rewrite PMap.gso; trivial.
    intros; simpl; trivial.
Qed.

Lemma loadbytes_D: forall m b ofs n bytes
      (LD: Mem.loadbytes m b ofs n = Some bytes),
      Mem.range_perm m b ofs (ofs + n) Cur Readable /\
      bytes = Mem.getN (nat_of_Z n) ofs (PMap.get b (Mem.mem_contents m)).
Proof. intros.
  Transparent Mem.loadbytes.
  unfold Mem.loadbytes in LD.
  Opaque Mem.loadbytes.
  remember (Mem.range_perm_dec m b ofs (ofs + n) Cur Readable) as d.
  destruct d; inv LD. auto.
Qed.

Lemma loadbytes_free m1 bf lo hi m2:
  Mem.free m1 bf lo hi = Some m2 ->
  forall n (b : block) (ofs : Z),
  b <> bf \/ lo >= hi \/ ofs + n <= lo \/ hi <= ofs ->
  Mem.loadbytes m2 b ofs n = Mem.loadbytes m1 b ofs n.
Proof. intros.
  remember (Mem.loadbytes m2 b ofs n) as d; symmetry in Heqd.
  destruct d.
  { apply loadbytes_D in Heqd; destruct Heqd.
    rewrite (Mem.free_result _ _ _ _ _ H) in H2. simpl in H2.
    assert (F: Mem.range_perm m1 b ofs (ofs + n) Cur Readable).
      red; intros. eapply Mem.perm_free_3. eassumption.
        eapply H1. assumption.
    apply Mem.range_perm_loadbytes in F. destruct F as [bytes F]; rewrite F.
    apply loadbytes_D in F. destruct F. rewrite <- H2 in H4. subst; trivial.
  }
  { remember (Mem.loadbytes m1 b ofs n) as q; symmetry in Heqq.
    destruct q; trivial.
    apply loadbytes_D in Heqq. destruct Heqq as [F C].
    assert (Mem.range_perm m2 b ofs (ofs + n) Cur Readable).
    { red; intros. eapply Mem.perm_free_1. eassumption.
        destruct H0. left; trivial. right. omega.
      apply F. trivial.
    }
    apply Mem.range_perm_loadbytes in H1. rewrite Heqd in H1. destruct H1; discriminate.
  }
Qed.

Lemma free_readonly: forall b lo hi m m'
      (M: Mem.free m b lo hi = Some m'),
      forall b, Mem.valid_block m b -> readonly m b m'.
Proof. red; intros.
destruct (zle n 0).
  split. repeat rewrite Mem.loadbytes_empty; trivial.
         intros; omega.
split.
  eapply loadbytes_free; try eassumption.
  destruct (eq_block b0 b); try subst b0. 2: left; trivial.
  right; destruct (zle hi lo). left; omega. right.
  destruct (zle (ofs + n) lo). left; trivial. right.
  destruct (zle hi ofs); trivial. exfalso.
  destruct (zle lo ofs).
    eapply (NWR 0); clear NWR. omega.
    (*eapply Mem.perm_max.*)
    eapply Mem.perm_implies.
      eapply Mem.free_range_perm; try eassumption. omega. constructor.
  eapply (NWR (lo - ofs)); clear NWR. omega. rewrite Zplus_minus.
    (*eapply Mem.perm_max.*)
    eapply Mem.perm_implies.
      eapply Mem.free_range_perm; try eassumption. omega. constructor.
intros. specialize (Mem.free_range_perm _ _ _ _ _ M); intros F. red in F.
    split; intros. eapply Mem.perm_free_1; try eassumption.
      destruct (eq_block b0 b); try subst b0. 2: left; trivial. right.
      destruct (zlt (ofs + i) lo). left; trivial. right. destruct (zle hi (ofs+i)). trivial.
      elim (NWR _ H0). (* specialize (size_chunk_pos chunk). intros; omega.*)
      (*eapply Mem.perm_max.*) eapply Mem.perm_implies. apply F. omega. constructor.
    eapply Mem.perm_free_3; try eassumption.
Qed.

Lemma unchanged_on_valid P m m' (HP: Mem.unchanged_on (fun b z => Mem.valid_block m b /\ P b z) m m'):
      Mem.unchanged_on P m m'.
Proof. destruct HP. split; trivial; intros. eauto.
  specialize (Mem.perm_valid_block _ _ _ _ _ H0); intros; eauto.
Qed.

Lemma unchanged_on_sub: forall (P Q: block -> BinInt.Z -> Prop) m m',
  Mem.unchanged_on Q m m' ->
  (forall b ofs, P b ofs -> Q b ofs) ->
  Mem.unchanged_on P m m'.
Proof.
intros until m'; intros [L H1 H2] H3.
split; intros.
auto.
solve[apply (H1 b ofs k p (H3 b ofs H)); auto].
solve[apply (H2 b ofs); auto].
Qed.

Lemma gsep_refl:
  forall {F V} j (ge: Genv.t F V),
    globals_separate ge j j.
Proof. intros ? ? mu ge b1 b2 d map1 map2. rewrite map1 in map2; discriminate. Qed.

Lemma gsep_mono {F1 V1 F2 V2:Type} (ge1:Genv.t F1 V1) (ge2:Genv.t F2 V2) j j' 
      (HG1: globals_separate  ge1 j j') 
      (G: forall b, isGlobalBlock ge2 b = true -> isGlobalBlock ge1 b = true): globals_separate ge2 j j'.
Proof. red; intros. specialize (HG1 _ _ _ H H0). 
  remember (isGlobalBlock ge2 b2) as p; destruct p; [symmetry in Heqp | trivial].
  rewrite (G _ Heqp) in HG1; discriminate.
Qed.

Lemma mem_forward_refl m: mem_forward m m.
Proof. split; trivial. Qed.

Lemma mem_forward_trans m m' m'' (M:mem_forward m m') (M':mem_forward m' m''): mem_forward m m''.
Proof. intros b B. destruct (M _ B) as [M1 M2]; clear M.
  destruct (M' _ M1) as [N1 N2]; clear M'.
  split; [trivial | eauto].
Qed.

Lemma mem_forward_unchanged_trans: forall P m1 m2 m3,
      Mem.unchanged_on P m1 m2 -> Mem.unchanged_on P m2 m3 ->
      mem_forward m1 m2 -> mem_forward m2 m3 ->
      mem_forward m1 m3 /\ Mem.unchanged_on P m1 m3.
Proof. intros.
split. eapply mem_forward_trans; eassumption.
split; intros.
+ eapply Ple_trans; eapply Mem.unchanged_on_nextblock; eassumption.
+ destruct H.
  destruct (unchanged_on_perm _ _ k p H3 H4).
  destruct H0. destruct (H1 _ H4).
  destruct (unchanged_on_perm0 _ _ k p H3 H0).
  split; intros; auto.
+ destruct H.
  rewrite <- (unchanged_on_contents _ _ H3 H4).
  destruct H0.
  apply (unchanged_on_contents0 _ _ H3).
  apply unchanged_on_perm; try assumption.
  apply Mem.perm_valid_block in H4. assumption.
Qed.

Lemma storebytes_mem_forward m b ofs bytes m' (ST: Mem.storebytes m b ofs bytes = Some m'):
      mem_forward m m'.
Proof. split.
+ eapply Mem.storebytes_valid_block_1; eauto.
+ intros. eapply Mem.perm_storebytes_2; eauto.
Qed.

Lemma alloc_mem_forward m lo hi b m' (A: Mem.alloc m lo hi = (m',b)):
      mem_forward m m'.
Proof. split.
+ eapply Mem.valid_block_alloc; eauto.
+ intros. eapply Mem.perm_alloc_4; eauto.
  intros ?; subst b0. apply Mem.perm_valid_block in H. 
  apply Mem.fresh_block_alloc in A; eauto.
Qed.

Lemma free_mem_forward m b lo hi m' (F: Mem.free m b lo hi = Some m'):
      mem_forward m m'.
Proof. split.
+ eapply Mem.valid_block_free_1; eauto.
+ intros. eapply Mem.perm_free_3; eauto.
Qed.

Lemma freelist_mem_forward: forall l m m' (F: Mem.free_list m l = Some m'),
      mem_forward m m'.
Proof. induction l; simpl; intros.
+ inv F. apply mem_forward_refl.
+ destruct a as [[b lo] hi]. 
  remember (Mem.free m b lo hi) as f; symmetry in Heqf; destruct f; try discriminate.
  apply IHl in F; clear IHl. apply free_mem_forward in Heqf.
  eapply mem_forward_trans; eauto.
Qed.

Lemma freelist_readonly: forall l m m'
      (M: Mem.free_list m l = Some m'),
      forall b, Mem.valid_block m b -> readonly m b m'.
Proof.
  induction l; simpl; intros.
    inv M. apply readonly_refl.
  destruct a. destruct p.
  remember (Mem.free m b0 z0 z) as d.
  destruct d; inv M; apply eq_sym in Heqd.
  specialize (IHl _ _ H1).
  eapply readonly_trans.
    eapply (free_readonly _ _ _ _ _ Heqd _ H).
  eapply IHl. eapply free_mem_forward; eassumption.
Qed.

Lemma loadbytes_unchanged_on (P : block -> Z -> Prop) m m' b ofs n:
  Mem.unchanged_on P m m' -> Mem.valid_block m b ->
  (forall i : Z, ofs <= i < ofs + n -> P b i) ->
  Mem.loadbytes m b ofs n = Mem.loadbytes m' b ofs n.
Proof. intros.
  symmetry. eapply Mem.loadbytes_unchanged_on_1; eauto.
Qed.

Lemma loadbytes_alloc_unchanged m1 lo hi m2 b :
  Mem.alloc m1 lo hi = (m2, b) ->
  forall n (b' : block) (ofs : Z),
  Mem.valid_block m1 b' ->
  Mem.loadbytes m2 b' ofs n = Mem.loadbytes m1 b' ofs n.
Proof. intros. symmetry.
  eapply loadbytes_unchanged_on; try eassumption.
  eapply (Mem.alloc_unchanged_on (fun bb z => True)). eassumption.
  simpl. trivial.
Qed.

Lemma alloc_readonly:
      forall m lo hi m' b
      (A: Mem.alloc m lo hi = (m',b)),
      forall b, Mem.valid_block m b -> readonly m b m'.
Proof. red; intros.
  split. eapply loadbytes_alloc_unchanged; try eassumption.
  intros; split. eapply Mem.perm_alloc_1; eassumption.
     intros. eapply Mem.perm_alloc_4; try eassumption.
     apply Mem.fresh_block_alloc in A.
     destruct (eq_block b0 b); trivial. subst. elim (A H).
Qed.

Lemma storebytes_readonly: forall m b ofs bytes m'
      (M: Mem.storebytes m b ofs bytes = Some m'),
      forall b, Mem.valid_block m b -> readonly m b m'.
Proof.
  red; intros.
  destruct (zle n 0).
  { split; intros. repeat rewrite Mem.loadbytes_empty; trivial. omega. }
  split.
    destruct bytes.
      eapply loadbytes_storebytes_nil; eassumption.
    eapply Mem.loadbytes_storebytes_other; try eassumption. omega.
    destruct (eq_block b0 b); subst. 2: left; trivial. right.
    apply Mem.storebytes_range_perm in M.
    destruct (zle (ofs0 + n) ofs). left; trivial. right.
    destruct (zle (ofs + Z.of_nat (length (m0 :: bytes)))  ofs0); trivial.
    exfalso. remember (Z.of_nat (length (m0 :: bytes))) as l. assert (0 < l). simpl in Heql. xomega. clear Heql.
    destruct (zle ofs0 ofs).
      apply (NWR (ofs-ofs0)). omega.
                  (*eapply Mem.perm_max.*) apply M. rewrite Zplus_minus. omega.
      elim (NWR 0). omega.
                  (*eapply Mem.perm_max.*) apply M. omega.
  split; intros. eapply Mem.perm_storebytes_1; eassumption. eapply Mem.perm_storebytes_2; eassumption.
Qed. 

Lemma freelist_valid_block: forall l m m' (L: Mem.free_list m l = Some m') b,
      Mem.valid_block m b <-> Mem.valid_block m' b.
Proof. induction l; simpl; intros.
+ inv L; split; trivial.
+ destruct a as [[bb lo] hi].
  remember (Mem.free m bb lo hi) as d; symmetry in Heqd.
  destruct d; inv L.
  split; intros. 
  - apply (IHl _ _ H0).
    eapply Mem.valid_block_free_1; eassumption.
  - eapply Mem.valid_block_free_2; [eassumption|].
    apply (IHl _ _ H0); trivial.
Qed. 
Lemma freelist_nextblock: forall l m m' (L: Mem.free_list m l = Some m'),
      (Mem.nextblock m) = (Mem.nextblock m').
Proof. induction l; simpl; intros.
+ inv L; trivial.
+ destruct a as [[bb lo] hi].
  remember (Mem.free m bb lo hi) as d; symmetry in Heqd.
  destruct d; inv L. apply IHl in H0. rewrite <- H0; clear IHl H0 l m'.
  apply Mem.nextblock_free in Heqd; rewrite Heqd; trivial.
Qed.

Lemma forward_refl {F V:Type} (ge:Genv.t F V) m: forward ge m m.
Proof. split; [ apply mem_forward_refl | apply RDOnly_fwd_refl ]. Qed.

Lemma forward_trans {F V:Type} (ge:Genv.t F V) m m' m'' (M: forward ge m m') (M': forward ge m' m''): forward ge m m''.
Proof. destruct M; destruct M'.
  split. eapply mem_forward_trans; eauto. eapply RDOnly_fwd_trans; eauto. 
Qed.

Lemma storebytes_forward {F V:Type} (ge:Genv.t F V)  m b ofs bytes m' (ST:Mem.storebytes m b ofs bytes = Some m')
      (RBV: forall b, ReadOnlyBlocks ge b = true -> Mem.valid_block m b):
      forward ge m m'.
Proof. split. eapply storebytes_mem_forward; eauto. 
  red; intros. eapply storebytes_readonly; eauto.
Qed.

Lemma alloc_forward {F V:Type} (ge:Genv.t F V) m lo hi m' b' (A:Mem.alloc m lo hi = (m', b'))
      (RBV: forall b, ReadOnlyBlocks ge b = true -> Mem.valid_block m b):
      forward ge m m'.
Proof. split. eapply alloc_mem_forward; eauto. 
  red; intros. eapply alloc_readonly; eauto.
Qed.

Lemma free_forward {F V:Type} (ge:Genv.t F V) m b lo hi m' (A:Mem.free m b lo hi = Some m')
      (RBV: forall b, ReadOnlyBlocks ge b = true -> Mem.valid_block m b):
      forward ge m m'.
Proof. split. eapply free_mem_forward; eauto. 
  red; intros. eapply free_readonly; eauto.
Qed.

Lemma freelist_forward {F V:Type} (ge:Genv.t F V): forall l m m' (A:Mem.free_list m l = Some m')
      (RBV: forall b, ReadOnlyBlocks ge b = true -> Mem.valid_block m b),
      forward ge m m'.
Proof. induction l; simpl; intros.
+ inv A. apply forward_refl.
+ destruct a as [[b lo] hi]. remember (Mem.free m b lo hi) as f; destruct f; [symmetry in Heqf | inv A].
  apply free_forward with (ge0:=ge) in Heqf; trivial.
  apply IHl in A; clear IHl.
  eapply forward_trans; eassumption.
  intros. apply RBV in H. apply Heqf; trivial.
Qed.

(*
(*This in particular should protect the readonly variables*)
Definition forward m1 m2 := mem_forward m1 m2
    /\ Mem.unchanged_on (fun b z => ~Mem.perm m1 b z Max Writable) m1 m2.


Lemma forward_mem_forward m m' (F: forward m m'): mem_forward m m'. 
Proof. apply F. Qed.

Lemma forward_refl m: forward m m.
Proof. split; [ apply mem_forward_refl | apply Mem.unchanged_on_refl]. Qed.

Lemma forward_trans m m' m'' (M: forward m m') (M': forward m' m''): forward m m''.
Proof. split. eapply mem_forward_trans. apply M. apply M'.
  apply unchanged_on_valid. 
  eapply Mem.unchanged_on_trans.
  + eapply Mem.unchanged_on_implies. apply M.
    intros; simpl. apply H.
  + eapply Mem.unchanged_on_implies. apply M'.
    intros; simpl. destruct H. intros N.
    destruct M. apply H1. apply H3; trivial.
Qed.


Lemma forward_unchanged_trans: forall P m1 m2 m3,
      Mem.unchanged_on P m1 m2 -> Mem.unchanged_on P m2 m3 ->
      forward m1 m2 -> forward m2 m3 ->
      forward m1 m3 /\ Mem.unchanged_on P m1 m3.
Proof. intros.
split. eapply forward_trans; eassumption.
eapply mem_forward_unchanged_trans; eauto; eapply forward_mem_forward; eauto.
Qed.
Lemma storebytes_forward m b ofs bytes m' (ST: Mem.storebytes m b ofs bytes = Some m'):
      forward m m'.
Proof.
split.
+ eapply storebytes_mem_forward; eauto.
+ eapply Mem.storebytes_unchanged_on. eauto.
  intros. intros N; apply N; clear N. eapply Mem.perm_cur.
  eapply Mem.storebytes_range_perm; eauto.
Qed.
Lemma alloc_forward m lo hi b m' (A: Mem.alloc m lo hi = (m',b)):
      forward m m'.
Proof. split.
+ eapply alloc_mem_forward; eauto.
+ eapply Mem.alloc_unchanged_on; eauto.
Qed. 
Lemma free_forward m b lo hi m' (F: Mem.free m b lo hi = Some m'):
      forward m m'.
Proof. split.
+ eapply free_mem_forward; eauto.
+ eapply Mem.free_unchanged_on; eauto.
  intros. intros N; apply N; clear N. eapply Mem.perm_implies. eapply Mem.perm_cur.
  eapply Mem.free_range_perm; eauto. constructor.
Qed.

Lemma freelist_forward: forall l m m' (F: Mem.free_list m l = Some m'),
      forward m m'.
Proof. intros.
split. eapply freelist_mem_forward; eauto.
eapply freelist_unchanged; eauto.
Qed.

Lemma freelist_unchanged: forall l m m' (F: Mem.free_list m l = Some m'),
      Mem.unchanged_on (fun b z => ~ Mem.perm m b z Max Writable) m m'.
Proof.
induction l; simpl; intros.
+ inv F. apply Mem.unchanged_on_refl.
+ destruct a as [[b lo] hi]. 
  remember (Mem.free m b lo hi) as f; symmetry in Heqf; destruct f; try discriminate.
  apply IHl in F; clear IHl. apply free_forward in Heqf.
  apply unchanged_on_valid.
  eapply Mem.unchanged_on_trans.
  - eapply Mem.unchanged_on_implies. apply Heqf.
    simpl; intros. apply H.
  - eapply Mem.unchanged_on_implies. apply F.
    simpl; intros. destruct Heqf. destruct H. destruct (H1 _ H).
    intros N. apply H5 in N. contradiction.
Qed.
*)

Lemma isep_compose m1 m2 m3 j1 j2 j1' j2' LM LT
      (Jvalid1 : forall b1 b2 d, j1 b1 = Some (b2, d) -> 
                        Mem.valid_block m1 b1 /\ Mem.valid_block m2 b2)
      (Jvalid2 : forall b2 b3 d, j2 b2 = Some (b3, d) -> 
                        Mem.valid_block m2 b2 /\ Mem.valid_block m3 b3)
      (LMT: forall b2 b3 d (J: j2 b2 =Some(b3,d)), LM b2 = LT b3)
      (Inc1: inject_incr j1 j1')
      (Inc2: inject_incr j2 j2')
      (ISep1: isep m1 j1 j1' m2 LM)
      (ISep2: isep m2 j2 j2' m3 LT):
  isep m1 (compose_meminj j1 j2) (compose_meminj j1' j2') m3 LT.
Proof. intros b1 b3 d J J'.
  apply compose_meminjD_Some in J'; destruct J' as [b2 [d1 [d2 [J1' [J2' D]]]]].
  apply compose_meminjD_None in J. destruct J as [J1 | [bb2 [dd2 [J1 J2]]]].
  + destruct (ISep1 _ _ _ J1 J1').
    split; trivial. intros. remember (j2 b2) as q; symmetry in Heqq; destruct q.
    - destruct p. specialize (Inc2 _ _ _ Heqq). rewrite J2' in Inc2; inv Inc2.
      destruct (Jvalid2 _ _ _ Heqq). rewrite <- (LMT _ _ _ Heqq). auto.
    - destruct (ISep2 _ _ _ Heqq J2'). auto.
  + rewrite (Inc1 _ _ _ J1) in J1'; inv J1'.
    destruct (ISep2 _ _ _ J2 J2'). destruct (Jvalid1 _ _ _ J1); contradiction.
Qed.

Lemma esep_compose m1 m2 m3 j1 j2 j1' j2' LM LT
      (Jvalid1 : forall b1 b2 d, j1 b1 = Some (b2, d) -> 
                        Mem.valid_block m1 b1 /\ Mem.valid_block m2 b2)
      (Jvalid2 : forall b2 b3 d, j2 b2 = Some (b3, d) -> 
                        Mem.valid_block m2 b2 /\ Mem.valid_block m3 b3)
      (LMT: forall b2 b3 d (J: j2 b2 =Some(b3,d)), LM b2 = LT b3)
      (Inc1: inject_incr j1 j1')
      (Inc2: inject_incr j2 j2')
      (ESep1: esep m1 j1 j1' m2 LM)
      (ESep2: esep m2 j2 j2' m3 LT):
  esep m1 (compose_meminj j1 j2) (compose_meminj j1' j2') m3 LT.
Proof. intros b1 b3 d J J'.
  apply compose_meminjD_Some in J'; destruct J' as [b2 [d1 [d2 [J1' [J2' D]]]]].
  apply compose_meminjD_None in J. destruct J as [J1 | [bb2 [dd2 [J1 J2]]]].
  + destruct (ESep1 _ _ _ J1 J1').
    split; trivial. intros. remember (j2 b2) as q; symmetry in Heqq; destruct q.
    - destruct p. specialize (Inc2 _ _ _ Heqq). rewrite J2' in Inc2; inv Inc2.
      destruct (Jvalid2 _ _ _ Heqq). rewrite <- (LMT _ _ _ Heqq). auto.
    - destruct (ESep2 _ _ _ Heqq J2'). auto.
  + rewrite (Inc1 _ _ _ J1) in J1'; inv J1'.
    destruct (ESep2 _ _ _ J2 J2'). destruct (Jvalid1 _ _ _ J1); contradiction.
Qed.

Lemma write_confined_compose j1 j2 (LM LT:Blockset) (m1 m1' m2 m2' m3 m3':mem)
      (local23 : forall b1 b2 d, j2 b1 = Some (b2, d) -> LM b1 = LT b2)
      (Conf12 : write_confined m1 m1' j1 LM m2 m2')
      (Conf23 : write_confined m2 m2' j2 LT m3 m3'):
  write_confined m1 m1' (compose_meminj j1 j2) LT m3 m3'.
Proof.
  intros W1 HW1 b3 z Vb3.
  destruct (Conf23 _ (Conf12 _ HW1) _ z Vb3) as [? | [? | [b2 [d2 [J2 [Loc2 | [b1 [d1 [J1 Wz]]]]]]]]]; clear Conf23 Conf12.
  left; trivial. right; left; trivial.
  right; left. rewrite <- (local23 _ _ _ J2); trivial.
  right; right. exists b1, (d2+d1). rewrite Z.sub_add_distr; split; [ rewrite Z.add_comm | trivial].
    unfold compose_meminj. rewrite J1, J2; trivial.
Qed.

Lemma globals_separate_compose_meminj {F2 V2 F3 V3:Type} (ge2 : Genv.t F2 V2) (ge3 : Genv.t F3 V3)
      (j1 j2 j1' j2': meminj)
      (GP23 : globals_preserved ge2 ge3 j2)
      (INC12 : inject_incr j1 j1')
      (Gsep12 : globals_separate ge2 j1 j1')
      (INC23 : inject_incr j2 j2')
      (Gsep23 : globals_separate ge3 j2 j2'):
  globals_separate ge3 (compose_meminj j1 j2) (compose_meminj j1' j2').
Proof.
intros b1 b3 d J J'. remember (isGlobalBlock ge3 b3) as g; destruct g; [ symmetry in Heqg; exfalso | trivial].
    apply compose_meminjD_Some in J'; destruct J' as [b2 [d1 [d2 [J1' [J2' D]]]]].
    unfold compose_meminj in J. remember (j1 b1) as q; symmetry in Heqq; destruct q; [ destruct p | ].
    + rewrite (INC12 _ _ _ Heqq) in J1'; inv J1'.
      remember (j2 b2) as w; destruct w; [destruct p; discriminate | symmetry in Heqw; clear J].
      rewrite (Gsep23 _ _ _  Heqw J2') in Heqg; discriminate. 
    + specialize (Gsep12 _ _ _ Heqq J1'). 
      remember (j2 b2) as t; destruct t; symmetry in Heqt.
      - destruct p; rewrite (INC23 _ _ _ Heqt) in J2'; inv J2'.
        rewrite <- (GP23 _ _ _ Heqt), Gsep12 in Heqg; discriminate.
      - rewrite (Gsep23 _ _ _ Heqt J2') in Heqg; discriminate.
Qed.

Lemma flatinj_E: forall b b1 b2 delta (H:Mem.flat_inj b b1 = Some (b2, delta)),
  b2=b1 /\ delta=0 /\ Plt b2 b.
Proof.
  unfold Mem.flat_inj. intros.
  destruct (plt b1 b); inv H. repeat split; trivial.
Qed.


Lemma empty_inj: Mem.inject (Mem.flat_inj 1%positive) Mem.empty Mem.empty.
Proof.
  split.
+  split. intros. destruct (flatinj_E _ _ _ _ H) as [? [? ?]]. subst.
          rewrite Zplus_0_r. assumption.
       intros. destruct (flatinj_E _ _ _ _ H) as [? [? ?]]. subst.
          apply Z.divide_0_r.
    intros. destruct (flatinj_E _ _ _ _ H) as [? [? ?]]. subst.
         exfalso. xomega.
+    intros. unfold Mem.flat_inj.
          remember (plt b 1).
          destruct s; trivial. xomega.
+   intros. destruct (flatinj_E _ _ _ _ H) as [? [? ?]]. subst.
         exfalso. xomega.
+   intros b; intros.
      destruct (flatinj_E _ _ _ _ H0) as [? [? ?]]. subst.
         exfalso. xomega.
+   intros.
      destruct (flatinj_E _ _ _ _ H) as [? [? ?]]. subst.
         exfalso. xomega.
+ intros.
      destruct (flatinj_E _ _ _ _ H) as [? [? ?]]. subst. rewrite Zplus_0_r in H0.
      left; trivial.
Qed.

Lemma empty_fwd: forall m, mem_forward Mem.empty m.
Proof. intros m b Vb.
   unfold Mem.valid_block in Vb. simpl in Vb. exfalso. xomega.
Qed.

Lemma meminj_no_overlap_rcni j k m (M:Mem.meminj_no_overlap j m)
   (I: inject_incr k j): Mem.meminj_no_overlap k m.
Proof. red; intros. apply I in H0. apply I in H1. eapply M; eauto. Qed.

Lemma full_ext_compose (j1 j2 j1' j2':meminj) (m1 m1' m2 m2':mem) (LS LM:Blockset)
      (Jvalid12 : forall b1 b2 d, j1' b1 = Some (b2, d) -> 
                  Mem.valid_block m1' b1 /\ Mem.valid_block m2' b2)
      (FE : full_ext LS j1 j2)
      (INC12 : inject_incr j1 j1')
      (INC23 : inject_incr j2 j2')
      (ISep12 : isep m1 j1 j1' m2 LM):
  full_ext (fun b : block => LS b || freshblockB m1 m1' b) j1' j2'.
Proof.
  intros b1 b2 d1 J1' Ext1. apply orb_false_iff in Ext1; destruct Ext1 as [LS1 Fresh1].
  destruct (Jvalid12 _ _ _ J1'). unfold freshblockB in Fresh1.
  destruct (valid_block_dec m1' b1); [ clear H | solve [contradiction]].
  destruct (valid_block_dec m1 b1); [ clear Fresh1 | simpl in Fresh1; congruence]. 
  remember (j1 b1) as j1b; symmetry in Heqj1b. destruct j1b.
+ destruct p; rewrite (INC12 _ _ _ Heqj1b) in J1'; inv J1'.
  destruct (FE _ _ _  Heqj1b LS1) as [b3 [d2 J2]]. exists b3, d2; apply INC23; trivial.
+ destruct (ISep12 _ _ _ Heqj1b J1'); contradiction.
Qed.

(*from mem_lemmas*)
Lemma val_inject_split:
  forall v1 v3 j12 j23 (V: val_inject (compose_meminj j12 j23) v1 v3),
    exists v2, val_inject j12 v1 v2 /\ val_inject j23 v2 v3.
Proof. intros.
   inv V.
     exists (Vint i). split; constructor.
     exists (Vlong i); split; constructor.
     exists (Vfloat f). split; constructor.
     exists (Vsingle f). split; constructor.
     apply compose_meminjD_Some in H. rename b2 into b3.
       destruct H as [b2 [ofs2 [ofs3 [J12 [J23 DD]]]]]; subst.
       eexists. split. econstructor. apply J12. reflexivity.
          econstructor. apply J23. rewrite Ptrofs.add_assoc.
          f_equal. rewrite Ptrofs.add_unsigned.
            apply Ptrofs.eqm_samerepr. 
            apply Ptrofs.eqm_add; apply Ptrofs.eqm_unsigned_repr.
     exists Vundef. split; constructor.
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
Lemma freshblockB_refl m: freshblockB m m = fun b => false.
Proof. unfold freshblockB. apply extensionality. intros b.
  destruct (valid_block_dec m b); simpl; trivial.
Qed.


Lemma memval_inject_id_refl: forall v, memval_inject inject_id v v.
Proof.
  destruct v. constructor. constructor. econstructor.
  destruct v; try econstructor. reflexivity. rewrite Ptrofs.add_zero. trivial.
Qed.


Lemma lessdef_valinject:
  forall v1 v2 v3 j (V12 : Val.lessdef v1 v2) (V23:val_inject j v2 v3),
    val_inject j v1 v3.
Proof.
  intros.
  inv V12; inv V23; try constructor.
    econstructor. eassumption. trivial.
Qed.

Lemma forall_lessdef_valinject:
  forall vals1 vals2 j (VInj12 : Forall2 Val.lessdef vals1 vals2) vals3
    (LD23 : Forall2 (val_inject j) vals2 vals3), Forall2 (val_inject j) vals1 vals3.
Proof. intros vals1 vals2 j VInj12.
   induction VInj12; intros; inv LD23. constructor.
     econstructor. eapply lessdef_valinject; eassumption.
          eapply (IHVInj12 _ H4).
Qed.

Lemma write_confined_confinedExt j (L:Blockset) (m1 m1' m2 m2' m3 m3':mem)
      (Conf12 : write_confined m1 m1' j L m2 m2')
      (Conf23 : write_confinedExt m2 m2' L m3 m3'):
  write_confined m1 m1' j L m3 m3'.
Proof.
  intros W1 HW1 b3 z Vb3.
  destruct (Conf23 _ (Conf12 _ HW1) _ z Vb3) as [UNCH | [HL | X]]; clear Conf23 Conf12.
  left; trivial. right; left; trivial. right; trivial.
Qed. 

Lemma freshblockB_1 m m' mm (B:forall b, Mem.valid_block m b <-> Mem.valid_block m' b):
      freshblockB m mm = freshblockB m' mm.
Proof. apply extensionality; intros b; unfold freshblockB.
      destruct (valid_block_dec mm b); simpl; trivial. 
      destruct (valid_block_dec m b); destruct (valid_block_dec m' b); simpl; trivial;
      apply B in v0; contradiction.
Qed.

Lemma freshblockB_2 m m' mm (B:forall b, Mem.valid_block m b <-> Mem.valid_block m' b):
      freshblockB mm m = freshblockB mm m'.
Proof. apply extensionality; intros b; unfold freshblockB.
      destruct (valid_block_dec m b); destruct (valid_block_dec m' b); simpl; trivial;
      try (apply B in v; contradiction).
Qed.

Lemma confinedExt_write_confined: forall (j : meminj) (LS LT : Blockset) (m1 m1' m2 m2' m3 m3' : mem)
      (HJ: forall b1 b2 d, j b1 = Some (b2, d) -> LS b1 = true -> LT b2 = true),
      write_confinedExt m1 m1' LS m2 m2' ->  write_confined m2 m2' j LT m3 m3' -> write_confined m1 m1' j LT m3 m3'.
Proof. intros. red; intros. remember (LT b2) as l; destruct l. right; left; trivial.
specialize (H X HX). specialize (H0 (fun b z => LS b = true \/ X b z)); simpl in H0.
destruct (H0 H _ z Hz) as [MU | [L | [b [d [J [Y | P]]]]]]. left; trivial. congruence. apply (HJ _ _ _ J) in Y; congruence.
right; right. exists b, d; split; trivial. Qed.

Lemma RDOnly_contravar m m' A (H:RDOnly_fwd m m' A) B (AB:forall b, B b = true -> A b = true): RDOnly_fwd m m' B.
Proof. red; intros. apply H. auto. Qed.

Lemma unchanged_on_empty P m: Mem.unchanged_on P Mem.empty m.
Proof. split; simpl; intros. xomega. unfold Mem.valid_block in H0; simpl in H0; xomega.
  apply Mem.perm_valid_block in H0. unfold Mem.valid_block in H0; simpl in H0; xomega.
Qed.