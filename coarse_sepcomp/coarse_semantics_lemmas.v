Require Import compcert.lib.Coqlib.
Require Import Memory.
Require Import Globalenvs.
Require Import VST.coarse_sepcomp.coarse_defs.
Require Import VST.coarse_sepcomp.coarse_base.
Require Import VST.coarse_sepcomp.coarse_semantics.

Lemma mem_step_mem_forward: forall m m', mem_step m m' -> mem_forward m m'.
Proof. induction 1.
+ eapply storebytes_mem_forward; eauto.
+ eapply alloc_mem_forward; eauto.
+ eapply freelist_mem_forward; eauto.
+ eapply mem_forward_trans; eauto.
Qed.

Lemma memstep_rdo {F V:Type} (ge: Genv.t F V):
forall m m', mem_step m m' ->
                  mem_respects_readonly ge m ->
                  (forall b, isGlobalBlock ge b = true -> Mem.valid_block m b) ->
                  RDOnly_fwd m m' (ReadOnlyBlocks ge).
Proof. intros; induction H; red; intros.
+ apply ReadOnlyBlocks_global in Hb.
  eapply storebytes_readonly; eauto.
+ apply ReadOnlyBlocks_global in Hb.
  eapply alloc_readonly; eauto.
+ apply ReadOnlyBlocks_global in Hb.
  eapply freelist_readonly; eauto.
+ apply mem_step_mem_forward in H.
  eapply readonly_trans.
  - apply IHmem_step1; trivial.
  - apply IHmem_step2; trivial.
    * eapply mem_respects_readonly_forward; eauto.
       intros. apply IHmem_step1; trivial. unfold ReadOnlyBlocks. rewrite H3; trivial.
    * intros. apply H; auto. 
Qed.

(*
Lemma mem_step_forward: forall m m', mem_step m m' -> forward m m'.
Proof. induction 1.
+ eapply storebytes_forward; eauto.
+ eapply alloc_forward; eauto.
+ eapply freelist_forward; eauto.
+ eapply forward_trans; eauto.
Qed.
*)

Lemma mem_step_validblock: forall m m', mem_step m m' -> 
  forall b, Mem.valid_block m b -> Mem.valid_block m' b.
Proof. intros m m' M. induction M.
eapply Mem.storebytes_valid_block_1; eassumption.
eapply Mem.valid_block_alloc; eassumption.
intros. eapply (freelist_valid_block _ _ _ H); eassumption.
intros. apply IHM2. apply IHM1; trivial.
Qed.
Lemma mem_step_nextblock: forall m m', mem_step m m' -> Ple (Mem.nextblock m) (Mem.nextblock m').
Proof. intros m m' M. induction M.
apply Mem.nextblock_storebytes in H; rewrite H; xomega.
apply Mem.nextblock_alloc in H; rewrite H; xomega.
rewrite (freelist_nextblock _ _ _ H); xomega.
xomega.
Qed.

Lemma mem_step_unchanged: forall m m', mem_step m m' ->  Mem.unchanged_on (fun b z => ~Mem.perm m b z Cur Writable) m m'.
Proof. (* intros.
 apply mem_step_forward in H. apply unchanged_on_valid. destruct H.
 eapply Mem.unchanged_on_implies. eapply H0.
 simpl; intros. intros N; apply H1.*)
 induction 1.
+ eapply Mem.storebytes_unchanged_on; eauto.
  intros. intros N. apply N; clear N.
  eapply Mem.storebytes_range_perm; eassumption.
+ eapply Mem.alloc_unchanged_on; eauto.
+ generalize dependent m'. generalize dependent m.
  induction l; simpl; intros.
  - inv H. apply Mem.unchanged_on_refl.
  - destruct a as [[b lo] hi]. remember (Mem.free m b lo hi) as k.
    destruct k; [symmetry in Heqk | congruence]. apply IHl in H.
    eapply Mem.unchanged_on_trans.
    * eapply Mem.free_unchanged_on; eauto.
      intros. intros N; apply N; clear N.
      eapply Mem.perm_implies. eapply Mem.free_range_perm; eauto. constructor.
    * eapply Mem.unchanged_on_implies; eauto.
      intros; simpl. intros N; apply H0; clear H0. eapply Mem.perm_free_3; eauto.
+ destruct IHmem_step1; destruct IHmem_step2. 
  split; intros. xomega.
  - destruct (unchanged_on_perm _ _ k p H1 H2) as [U1 U2]. 
    destruct (unchanged_on_perm0 b ofs k p) as [W1 W2].
    * intros N. apply unchanged_on_perm in N; eauto.
    * red; red in H2. xomega.
    * split; eauto.
  - rewrite <- (unchanged_on_contents _ _ H1 H2). 
    assert (X:= Mem.perm_valid_block _ _ _ _ _ H2). 
    apply unchanged_on_contents0.
    * intros N. apply H1. apply unchanged_on_perm; trivial.
    * apply unchanged_on_perm; trivial.
Qed. 

Lemma memstep_forward {F V:Type} (ge:Genv.t F V): 
      forall m m' (M: mem_step m m') (RBV: forall b, ReadOnlyBlocks ge b = true -> Mem.valid_block m b), forward ge m m'.
Proof. induction 1.
+ eapply storebytes_forward; eauto.
+ eapply alloc_forward; eauto.
+ eapply freelist_forward; eauto.
+ intros. specialize (IHM1 RBV). eapply forward_trans; eauto.
  apply IHM2. intros. apply RBV in H; apply IHM1; trivial.
Qed.

  Lemma Ncorestep {G C} (Sem : @MemSem G C) g:
    forall n c1 m1 c3 m3, corestepN Sem g (S n) c1 m1 c3 m3 <->
    exists c2 m2, corestepN Sem g n c1 m1 c2 m2 /\ corestep Sem g c2 m2 c3 m3.
  Proof. induction n.
   + simpl; intros.
     split; intros.
     - destruct H as [c [m [X Y]]]; inv Y. 
       do 2 eexists; split. reflexivity. eassumption.
     - destruct H as [c [m [X Y]]]. inv X.
       do 2 eexists; split. eassumption. reflexivity.
   + intros. 
     split; intros. 
     - destruct H as [c [m [X Y]]].
       destruct (IHn c m c3 m3) as [Q _]; clear IHn.
       destruct (Q Y) as [cc [mm [P T]]]; clear Q Y.
       do 2 eexists; split; eauto.
       simpl. do 2 eexists; split; eassumption.
     - destruct H as [c [m [[c2 [m2 [P Q]]] Y]]].
       simpl. exists c2, m2. split; trivial. clear P.
       destruct (IHn c2 m2 c3 m3) as [_ IH]; clear IHn.
       simpl in IH. destruct IH as [c4 [m4 [STP STPN]]].
       { do 2 eexists; split; eauto. }
       do 2 eexists; split; eauto.
  Qed.

  Lemma steps_iter {G C} (Sem : @MemSem G C) g ci mi
        (Steps : forall i, corestep Sem g (ci i) (mi i) (ci (S i)) (mi (S i))):
  forall n, corestepN Sem g (S n) (ci O) (mi O) (ci (S n)) (mi (S n)).
  Proof. induction n; simpl; intros.
  + do 2 eexists. split. apply Steps. split; reflexivity.
  + specialize (Steps (S n)).
    simpl in IHn. destruct IHn as [c [m [STEP STEPS]]].
    exists c, m; split; trivial. clear STEP.
    remember (ci (S n)) as d; clear Heqd. remember (mi (S n)) as p; clear Heqp.
    remember (ci (S (S n))) as e; clear Heqe. remember (mi (S (S n))) as q; clear Heqq.
    specialize (Ncorestep Sem g n c m e q); intros [_ A].
    destruct A as [cc [mm [X Y]]].
    { do 2 eexists; split; eauto. }
    do 2 eexists; split; eauto.
  Qed.