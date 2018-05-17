Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import compcert.common.Values.
Require Import compcert.common.Events. (*needed for standard definitions of 
                        mem_unchanged_on,loc_out-of_bounds etc etc*)
Require Import compcert.common.Memory.
Require Import compcert.lib.Maps.
Require Import VST.msl.Axioms.

Goal forall m b ofs p (H: ~ Mem.perm m b ofs p Nonempty), PMap.get b (Mem.mem_access m) ofs p = None.
intros. unfold Mem.perm in *.
remember (PMap.get b (Mem.mem_access m) ofs p) as pp.
destruct pp; simpl in *. exfalso. apply H. apply perm_any_N.
trivial.
Qed.

Definition isSource j m1 (b2:block) (ofs2:Z) b : option Z :=
  match j b with None => None
         | Some (bb,delta) => if eq_block b2 bb 
                                             then if Mem.perm_dec m1 b (ofs2 - delta) Max Nonempty 
                                                     then Some (ofs2 - delta)  else None
                                             else None
  end.

Lemma isSource_NoneE: forall j m b2 ofs2 b1, None = isSource j m b2 ofs2 b1 ->
    j b1 = None \/ (exists b, exists delta, j b1 = Some (b,delta) /\ b<>b2) \/
    (exists delta, j b1 = Some(b2,delta) /\ ~ Mem.perm m b1 (ofs2-delta) Max Nonempty).
Proof. intros. unfold isSource in H.
  remember (j b1) as zz.
  destruct zz. destruct p.
     destruct (eq_block b2 p). subst.
       remember (Mem.perm_dec m b1 (ofs2 - z) Max Nonempty) as d.
       destruct d; inv H. right. right. exists z. split; trivial. 
     right. left. exists p. exists z. split; auto. 
  left; trivial. 
Qed.

Lemma isSource_SomeE: forall j m b2 ofs2 b1 ofs1, Some ofs1 = isSource j m b2 ofs2 b1 ->
    exists delta, j b1 = Some(b2,delta) /\ Mem.perm m b1 ofs1 Max Nonempty /\ ofs2=ofs1+delta.
Proof. intros. unfold isSource in H.
  remember (j b1) as zz.
  destruct zz. destruct p.
     destruct (eq_block b2 p). subst.
       remember (Mem.perm_dec m b1 (ofs2 - z) Max Nonempty) as d.
       destruct d; inv H. exists z. split; trivial. split; trivial. omega.
    inv H.
  inv H.
Qed.

Lemma isSource_SomeI: forall j m b2 ofs2 b1 delta, 
       j b1 = Some(b2,delta) -> Mem.perm m b1 (ofs2 - delta) Max Nonempty ->
        isSource j m b2 ofs2 b1 = Some (ofs2-delta).
Proof. intros. unfold isSource. rewrite H.
     destruct (eq_block b2 b2). subst.
       remember (Mem.perm_dec m b1 (ofs2 - delta) Max Nonempty) as d.
       destruct d. trivial.  exfalso. apply (n H0).
     exfalso. apply n. trivial.
Qed.

Lemma isSource_SomeI': forall j m b2 ofs1 b1 delta, 
       j b1 = Some(b2,delta) -> Mem.perm m b1 ofs1 Max Nonempty ->
        isSource j m b2 (ofs1+delta) b1 = Some ofs1.
Proof. intros. unfold isSource. rewrite H.
     destruct (eq_block b2 b2). subst.
       assert (ofs1 = ofs1 + delta - delta). omega. rewrite <- H1.
       remember (Mem.perm_dec m b1 ofs1 Max Nonempty) as d.
       destruct d. trivial.  exfalso. apply (n H0).
     exfalso. apply n. trivial.
Qed.
Require Import Coq.PArith.BinPos.

Definition sourceN (n:block) (j:meminj) (m:mem)
                   (b2:block) (ofs2:Z): option(block * Z) :=
Pos.peano_rect
            (fun p => option(block * Z))
            (match isSource j m b2 ofs2 1%positive
             with Some ofs1 => Some(1%positive, ofs1)
                | None => None
             end)
            (fun p Hp => match isSource j m b2 ofs2 (Pos.succ p)
             with Some ofs1 => Some (Pos.succ p, ofs1)
                | None => Hp
             end) 
            n.

Lemma sourceN_SomeE: forall j m b2 ofs2 n b1 ofs1, 
    sourceN n j m b2 ofs2 = Some(b1,ofs1) ->
    exists delta, (b1 <= n)%positive /\ j b1 = Some(b2,delta) /\ 
                  Mem.perm m b1 ofs1 Max Nonempty /\ ofs2=ofs1+delta.
Proof. intros j m b2 ofs. 
apply (Pos.peano_ind 
         (fun p => forall (b1 : block) (ofs1 : Z),
              sourceN p j m b2 ofs = Some (b1, ofs1) ->
              exists delta : Z,
              (b1 <= p)%positive /\
              j b1 = Some (b2, delta) /\
              Mem.perm m b1 ofs1 Max Nonempty /\ ofs = ofs1 + delta)).
intros.
  unfold sourceN in H. rewrite Pos.peano_rect_base in H.
  remember (isSource j m b2 ofs 1%positive) as d.
  destruct d; inv H.
     apply isSource_SomeE in Heqd.
     destruct Heqd as [delta [J [P Off]]].
     exists delta.
     repeat split; auto; xomega.
intros.
  unfold sourceN in H0.
  rewrite Pos.peano_rect_succ in H0.
  remember (isSource j m b2 ofs (Pos.succ p)) as d.
  destruct d. inv H0. clear H.
     apply isSource_SomeE in Heqd.
     destruct Heqd as [delta [J [P Off]]].
     exists delta.
     repeat split; auto; xomega.
  specialize (H _ _ H0). clear H0.
     destruct H as [delta [D [J [P Off]]]].
     exists delta.
     repeat split; auto; xomega.
Qed.

Lemma sourceN_NoneE: forall j m b2 ofs2 n, 
    sourceN n j m b2 ofs2 = None -> 
    forall b1 delta, (b1 <= n)%positive -> j b1 = Some(b2,delta) ->
                     ~ Mem.perm m b1 (ofs2-delta) Max Nonempty.
Proof. intros j m b2 ofs2.
apply (Pos.peano_ind 
         (fun p => sourceN p j m b2 ofs2 = None ->
              forall (b1 : positive) (delta : Z),
              (b1 <= p)%positive ->
              j b1 = Some (b2, delta) ->
              ~ Mem.perm m b1 (ofs2 - delta) Max Nonempty)).
intros. assert (b1 = 1%positive). xomega. subst. clear H0. 
  unfold sourceN in H. rewrite Pos.peano_rect_base in H.
  remember (isSource j m b2 ofs2 1%positive) as d.
  destruct d. inv H.
  apply isSource_NoneE in Heqd.
  destruct Heqd. congruence. 
  destruct H0. destruct H0 as [b [delta1 [J P]]]. 
                rewrite J in H1. inv H1. exfalso. apply P. trivial. 
    destruct H0 as [ddelta [J P]]. rewrite J in H1. inv H1. assumption. 
intros.
  unfold sourceN in H0.
  rewrite Pos.peano_rect_succ in H0.
  remember (isSource j m b2 ofs2 (Pos.succ p)) as d.
  destruct d. inv H0. 
  specialize (H H0). clear H0.
  apply isSource_NoneE in Heqd.
  destruct Heqd.
    apply H; trivial. 
    destruct (peq b1 (Pos.succ p)). 
      subst. congruence.
      xomega. 
  destruct H0. destruct H0 as [b [delta1 [J P]]]. 
    apply H; trivial. 
    destruct (peq b1 (Pos.succ p)). 
      subst. congruence.
      xomega. 
   destruct H0 as [ddelta [J P]].
    destruct (peq b1 (Pos.succ p)). 
      subst. rewrite J in H2. inv H2. assumption.
    apply H; trivial. xomega.
Qed.  

Lemma sourceN_SomeI: forall n j m b2 b1 ofs1 delta (OV:Mem.meminj_no_overlap j m),
   j b1 = Some(b2,delta) -> Mem.perm m b1 ofs1 Max Nonempty ->
   (b1 <= n)%positive ->
   sourceN n j m b2 (ofs1+delta) = Some(b1,ofs1).
Proof. intros. 
  remember (sourceN n j m b2 (ofs1 + delta)) as src.
  destruct src; apply eq_sym in Heqsrc. 
  Focus 2. assert (ZZ:= sourceN_NoneE _ _ _ _ _ Heqsrc _ _ H1 H).
           exfalso. assert (ofs1 + delta - delta = ofs1). omega.
                    rewrite H2 in ZZ. apply (ZZ H0).
  (*Some*) destruct p as [b off].
       apply sourceN_SomeE in Heqsrc.
       destruct Heqsrc as [d [Hd [J [P X]]]].
       destruct (eq_block b1 b).
          subst. rewrite H in J. inv J.
          assert (ofs1 = off). omega. subst. trivial.
       destruct (OV _ _ _ _ _ _ _ _ n0 H J H0 P).
          exfalso. apply H2; trivial.
       rewrite X in H2. exfalso. apply H2. trivial.
Qed.  

Definition  source j m (b2:block) (ofs2:Z) : option(block * Z) :=
   if plt 1%positive (Mem.nextblock m) 
   then sourceN (Pos.pred (Mem.nextblock m)) j m b2 ofs2
   else None.

Lemma perm_nextblock_gt_1: forall m b ofs k p (P: Mem.perm m b ofs k p),
  Plt 1 (Mem.nextblock m).
Proof.
  intros. apply Mem.perm_valid_block in P. 
  unfold Mem.valid_block in P. xomega.
Qed.

Lemma source_SomeE: forall j m (b2:block) (ofs2:Z) p, 
  Some p = source j m b2 ofs2 -> 
    exists b1, exists delta, exists ofs1, 
                  p = (b1,ofs1) /\
                  (b1 < Mem.nextblock m)%positive /\ j b1 = Some(b2,delta) /\ 
                  Mem.perm m b1 ofs1 Max Nonempty /\ ofs2=ofs1+delta.
Proof. intros.
  unfold source in H. destruct p as [b1 ofs1]; subst. apply eq_sym in H.
  destruct (plt 1 (Mem.nextblock m)).
    apply sourceN_SomeE in H. 
    destruct H as [delta [Bounds [J [P Off]]]]; subst. 
    exists b1; exists delta; exists ofs1. split; trivial. 
    split. specialize (Ppred_Plt (Mem.nextblock m)). xomega.
    repeat split; auto.
  inv H.
Qed.
  
Lemma source_NoneE: forall j m b2 ofs2, 
    None = source j m b2 ofs2 -> 
    forall b1 delta, (b1 < Mem.nextblock m)%positive -> j b1 = Some(b2,delta) ->
                     ~ Mem.perm m b1 (ofs2-delta) Max Nonempty. 
Proof. intros. apply eq_sym in H. unfold source in H.     
  destruct (plt 1 (Mem.nextblock m)).
    eapply (sourceN_NoneE _ _ _ _ _ H b1 delta); trivial. 
    destruct (Pos.succ_pred_or (Mem.nextblock m)); xomega.
  exfalso. xomega.
Qed.  

Lemma source_SomeI: forall j m b2 b1 ofs1 delta (OV:Mem.meminj_no_overlap j m),
   j b1 = Some(b2,delta) -> Mem.perm m b1 ofs1 Max Nonempty ->
   source j m b2 (ofs1+delta) = Some(b1,ofs1).
Proof. intros. unfold source.
  destruct (plt 1 (Mem.nextblock m)).
    unfold Coqlib.Plt in p.
    eapply sourceN_SomeI. apply OV. apply H. apply H0.
    apply Mem.perm_valid_block in H0. unfold Mem.valid_block in H0.
    remember (Mem.nextblock m) as b. clear H OV Heqb m ofs1 j b2 delta.
      destruct (Pos.succ_pred_or b); xomega.
  specialize (perm_nextblock_gt_1 _ _ _ _ _ H0). contradiction.
Qed.

Lemma sourceNone_LOOR: forall j m1 b2 ofs2 (N: None = source j m1 b2 ofs2) m2
              (Inj12: Mem.inject j m1 m2), loc_out_of_reach j m1 b2 ofs2.
Proof. intros. intros b1; intros.
   eapply source_NoneE; try eassumption.
     apply (Mem.valid_block_inject_1 _ _ _ _ _ _ H Inj12).
Qed.

Lemma memvalUnchOnR: forall m1 m2 m3 m3' b ofs 
  (n : ~ Mem.perm m1 b ofs Max Nonempty)
  (UnchOn13 : Mem.unchanged_on (loc_out_of_bounds m1) m3 m3')
  (MV : memval_inject inject_id
                (ZMap.get ofs (PMap.get b (Mem.mem_contents m2)))
                (ZMap.get ofs (PMap.get b (Mem.mem_contents m3))))
   (Rd: Mem.perm m3 b ofs Cur Readable),
   memval_inject inject_id (ZMap.get ofs (PMap.get b (Mem.mem_contents m2)))
     (ZMap.get ofs (PMap.get b (Mem.mem_contents m3'))).
Proof. intros. 
  destruct UnchOn13 as [_ _ U].
  rewrite (U _ _ n Rd).
  apply MV.
Qed.

Lemma perm_order_total: forall p1 p2, perm_order p1 p2 \/ perm_order p2 p1.
Proof. intros. 
  destruct p1; destruct p2; try (left; constructor) ; try (right; constructor).
Qed.

Lemma perm_order_antisym: forall p1 p2, perm_order p1 p2 -> perm_order p2 p1 -> p1=p2.
Proof. intros. inv H; inv H0; trivial.  Qed.

Lemma po'_E: forall p q, Mem.perm_order' p q -> exists pp, p=Some pp.
Proof. intros. destruct p; simpl in H. exists p; trivial. contradiction. Qed.

Lemma  perm_refl_1: forall p1 p1'  (HP:forall p, perm_order p1' p -> perm_order p1 p), perm_order p1 p1'.
Proof. intros. apply HP. apply perm_refl. Qed.

Lemma free_E: forall p, perm_order p Freeable -> p = Freeable.
Proof. intros. inv H; trivial. Qed.

Lemma  write_E: forall p, perm_order p Writable -> p=Freeable \/ p=Writable.
Proof. intros. inv H. right; trivial. left; trivial. Qed.

Lemma perm_split: forall m b ofs (A B: Prop) k p 
              (SPLIT: (Mem.perm m b ofs k p -> A) /\ (~Mem.perm m b ofs k p -> B)) 
              (P:Prop)
              (HA: Mem.perm m b ofs k p -> A -> P)
              (HB: ~Mem.perm m b ofs k p -> B -> P), P.
Proof. intros. destruct SPLIT.
   destruct (Mem.perm_dec m b ofs k p); auto.
Qed.

Lemma perm_splitA: forall m b ofs k' p m2' m2 m3' k b3 ofs3
              (SPLIT: (Mem.perm m b ofs k' p-> PMap.get b (Mem.mem_access m2') ofs k = PMap.get b (Mem.mem_access m2) ofs k) /\
                             (~Mem.perm m b ofs k' p -> PMap.get b (Mem.mem_access m2') ofs k = PMap.get b3 (Mem.mem_access m3') ofs3 k)) 
              (P:Prop)
              (HA: Mem.perm m b ofs k' p -> Mem.perm m2' b ofs k = Mem.perm m2 b ofs k -> P)
              (HB: ~Mem.perm m b ofs k' p -> Mem.perm m2' b ofs k = Mem.perm m3' b3 ofs3 k  -> P), P.
Proof. intros. destruct SPLIT.
   destruct (Mem.perm_dec m b ofs k' p).
          apply (HA p0). unfold Mem.perm. rewrite (H p0). reflexivity . 
          apply (HB n). unfold Mem.perm. rewrite (H0 n). reflexivity . 
Qed.

Lemma valid_splitA: forall (m m2' m2 m1':mem) (b:block) ofs k
              (SPLIT: if plt b (Mem.nextblock m) 
                             then PMap.get b (Mem.mem_access m2') ofs k = PMap.get b (Mem.mem_access m2) ofs k 
                             else PMap.get b (Mem.mem_access m2') ofs k = PMap.get b (Mem.mem_access m1') ofs k)
               P
              (HA: Mem.valid_block m b -> Mem.perm m2' b ofs k = Mem.perm m2 b ofs k -> P)
              (HB: ~Mem.valid_block m b -> Mem.perm m2' b ofs k = Mem.perm m1' b ofs k -> P), P.
Proof. intros.
   remember (plt b (Mem.nextblock m)) as d. unfold Mem.perm in *.
   destruct d; clear Heqd; rewrite SPLIT in *; auto.
Qed.

Lemma valid_splitC: forall (T:Type)(m:mem) (b:block) X (A B:T)
              (SPLIT: if plt b (Mem.nextblock m) 
                             then X = A
                             else X = B)
               P
              (HA: Mem.valid_block m b -> X=A -> P)
              (HB: ~Mem.valid_block m b -> X=B -> P), P.
Proof. intros.
   remember (plt b (Mem.nextblock m)) as d.
   destruct d; clear Heqd; rewrite SPLIT in *; auto.
Qed.

Lemma dec_split: forall {C} (dec: C \/ ~ C) (A B: Prop)
              (SPLIT: (C -> A) /\ (~C -> B)) 
              (P:Prop)
              (HA: C -> A -> P)
              (HB: ~C -> B -> P), P.
Proof. intros. destruct SPLIT.
   destruct dec; auto.
Qed.

Lemma valid_split: forall m b (A B: Prop)
              (SPLIT: (Mem.valid_block m b  -> A) /\ (~Mem.valid_block m b -> B)) 
              (P:Prop)
              (HA: Mem.valid_block m b -> A -> P)
              (HB: ~Mem.valid_block m b -> B -> P), P.
Proof. intros. eapply dec_split; try eassumption. unfold Mem.valid_block. xomega. Qed.

Lemma perm_subst: forall b1 b2 m1 m2 ofs1 ofs2 k
     (H: PMap.get b1 (Mem.mem_access m1) ofs1 k = PMap.get b2 (Mem.mem_access m2) ofs2 k),
     Mem.perm m1 b1 ofs1 k = Mem.perm m2 b2 ofs2 k.
Proof. intros. unfold Mem.perm. rewrite H. reflexivity. Qed.


Definition extern_of (j:meminj) (L: block -> bool) : meminj :=
  fun b => if L b then None else j b.

Lemma extern_of_Itrue j L b (HL:L b = true): extern_of j L b = None.
Proof. unfold extern_of; rewrite HL; trivial. Qed.

Lemma extern_of_Ifalse j L b (HL: L b = false): extern_of j L b = j b.
Proof. unfold extern_of; rewrite HL; trivial. Qed.

Lemma extern_of_INone j L b (Hb: j b = None): extern_of j L b = None.
Proof. unfold extern_of; rewrite Hb. destruct (L b); trivial. Qed.

Lemma extern_of_ESome j L b p (E: extern_of j L b = Some p): L b = false /\ j b = Some p.
Proof. unfold extern_of in E. destruct (L b); inv E. split; trivial. Qed.

Lemma extern_of_ENone j L b (E: extern_of j L b = None): L b = true \/ j b = None.
Proof. unfold extern_of in E. destruct (L b); inv E. left; trivial. right; trivial. Qed.

Lemma compose_meminj_extern' j12 L1 j23 L2
      (HL: forall b1 b2 d, j12 b1 = Some (b2,d) -> L1 b1 = false -> L2 b2 = false):
      compose_meminj (extern_of j12 L1) (extern_of j23 L2) = 
      extern_of (compose_meminj j12 j23) L1.
Proof. unfold compose_meminj, extern_of. extensionality b.
remember (L1 b) as q. destruct q; trivial. symmetry in Heqq.
remember (j12 b) as w. destruct w; trivial. destruct p.
rewrite (HL b b0 z); try (symmetry; eassumption); trivial.
Qed.

Lemma compose_meminj_extern j12 L1 j23 L2
      (HL: forall b1 b2 d, j12 b1 = Some (b2,d) -> L1 b1 = L2 b2):
      compose_meminj (extern_of j12 L1) (extern_of j23 L2) = 
      extern_of (compose_meminj j12 j23) L1.
Proof. apply compose_meminj_extern'. intros. rewrite <- (HL _ _ _ H); trivial. Qed.

Definition local_of (j:meminj) (L: block -> bool) : meminj :=
  fun b => if L b then j b else None.

Lemma local_of_Itrue j L b (HL:L b = true): local_of j L b = j b.
Proof. unfold local_of; rewrite HL; trivial. Qed.

Lemma local_of_Ifalse j L b (HL: L b = false): local_of j L b = None.
Proof. unfold local_of; rewrite HL; trivial. Qed.

Lemma local_of_INone j L b (Hb: j b = None): local_of j L b = None.
Proof. unfold local_of; rewrite Hb. destruct (L b); trivial. Qed.

Lemma local_of_ESome j L b p (E: local_of j L b = Some p): L b = true/\ j b = Some p.
Proof. unfold local_of in E. destruct (L b); inv E. split; trivial. Qed.

Lemma local_of_ENone j L b (E: local_of j L b = None): L b = false \/ j b = None.
Proof. unfold local_of in E. destruct (L b); inv E. right; trivial. left; trivial. Qed.

Lemma compose_meminj_local' j12 L1 j23 L2
      (HL: forall b1 b2 d, j12 b1 = Some (b2,d) -> L1 b1 = true -> L2 b2 = true):
      compose_meminj (local_of j12 L1) (local_of j23 L2) = 
      local_of (compose_meminj j12 j23) L1.
Proof. unfold compose_meminj, local_of. extensionality b.
remember (L1 b) as q. destruct q; trivial. symmetry in Heqq.
remember (j12 b) as w. destruct w; trivial. destruct p.
rewrite (HL b b0 z); try (symmetry; eassumption); trivial.
Qed.

Lemma compose_meminj_local j12 L1 j23 L2
      (HL: forall b1 b2 d, j12 b1 = Some (b2,d) -> L1 b1 = L2 b2):
      compose_meminj (local_of j12 L1) (local_of j23 L2) = 
      local_of (compose_meminj j12 j23) L1.
Proof. apply compose_meminj_local'. intros. rewrite <- (HL _ _ _ H); trivial. Qed.

Definition join (j k:meminj):meminj := fun b =>
  match j b with
     Some (b1, delta) => Some (b1,delta)
   | None => k b
  end.

Definition disjoint (j k:meminj):Prop :=
    forall b, j b = None \/ k b = None.

Lemma join_assoc: forall f g h, join f (join g h) = join (join f g) h.
Proof. intros. unfold join.
  extensionality b.
  destruct (f b); trivial. destruct p. trivial.
Qed.  

Lemma join_com: forall f g, disjoint f g -> join f g = join g f.
Proof. intros. unfold join.
extensionality b.
destruct (H b); rewrite H0.
  destruct (g b); intuition. 
  destruct (f b); intuition.
Qed. 

Lemma disjoint_com: forall f g, disjoint f g <-> disjoint g f.
Proof. intros. unfold disjoint.
 split; intros. destruct (H b); intuition. destruct (H b); intuition.
Qed.

Lemma disjoint_sub: forall j k (D: disjoint j k) j' k'
              (J: inject_incr j' j) (K:inject_incr k' k),
              disjoint j' k'.
Proof. intros.
  intros b.
  remember (j' b) as d.
  destruct d; try (left; reflexivity).
  apply eq_sym in Heqd; destruct p.
  remember (k' b) as q.
  destruct q; try (right; reflexivity).
  apply eq_sym in Heqq; destruct p.
  specialize (D b).
  rewrite (J _ _ _ Heqd) in D.
  rewrite (K _ _ _ Heqq) in D.
  destruct D; inv H.
Qed.

Lemma joinI: forall f g b p
             (Hp: f b = Some p \/ (f b = None /\ g b = Some p)),
      join f g b = Some p.
Proof. intros. unfold join.
  destruct Hp as [Hf | [Hf Hg]]; rewrite Hf; trivial.
    destruct p; trivial.
Qed.

Lemma joinD: forall j k (D: disjoint j k) b,
   match join j k b with
     Some(b1,delta) => (j b = Some(b1,delta) /\ k b = None) \/
                       (k b = Some(b1,delta) /\ j b = None)
   | None => j b = None /\ k b = None
  end.
Proof. intros.
  unfold join. destruct (D b); rewrite H.
     case_eq (k b); eauto.
     destruct p; eauto.
   case_eq (j b); eauto.
     destruct p; eauto. 
Qed.

Lemma joinD_Some:
      forall j k b b' delta (J: join j k b = Some(b',delta)),
      j b = Some(b',delta) \/ (j b = None /\ k b = Some(b',delta)).
Proof. intros. unfold join in J.
  remember (j b) as d.
  destruct d; apply eq_sym in Heqd.
    destruct p; left. assumption.
  right; split; auto. 
Qed.

Lemma joinD_None:
      forall j k b (J: join j k b = None),
      j b = None /\ k b = None.
Proof. intros. unfold join in J.
  remember (j b) as d.
  destruct d; apply eq_sym in Heqd; auto.
    destruct p. inv J. 
Qed.


Lemma joinI_None: forall j k b (J:j b = None) (K:k b = None),
                  join j k b = None.
Proof. intros.
  unfold join. rewrite J. assumption. 
Qed.

Lemma inject_incr_join: forall j j' k k'
  (J: inject_incr j j') (K: inject_incr k k')
  (D: disjoint j' k'),
  inject_incr (join j k) (join j' k').
Proof. intros.
  intros b; intros.
  unfold join in *.
  remember (j b) as d.
  destruct d; apply eq_sym in Heqd.
      destruct p. inv H.
      rewrite (J _ _ _ Heqd).
      trivial.
  destruct (D b).
    rewrite H0. apply K. apply H.
  rewrite (K _ _ _ H) in H0. inv H0.
Qed.

Lemma join_incr_left: forall j k, inject_incr j (join j k).
Proof. intros. intros b; intros.
  unfold join; rewrite H; trivial.
Qed.

Lemma join_incr_right: forall j k (D:disjoint j k), 
                       inject_incr k (join j k).
Proof. intros. intros b; intros.
  unfold join.
  destruct (D b) as [K | K]; rewrite K in *. trivial.
  inv H.
Qed.

Lemma disjointD_left: 
      forall j k b b' delta (J: j b = Some (b',delta)) 
             (D:disjoint j k), k b = None.
Proof. intros.
  destruct (D b) as [K | K]; rewrite K in *. inv J. trivial.
Qed. 

Lemma disjointD_right:
      forall j k b b' delta (K: k b = Some (b',delta))
             (D:disjoint j k), j b = None.
Proof. intros.
  destruct (D b) as [J | J]; rewrite J in *. trivial. inv K.
Qed.

Lemma join_left_agree: 
      forall j k b b1 d1 (JK: join j k b = Some(b1,d1))
             b2 d2 (J: j b = Some(b2,d2)), 
      b1=b2 /\ d1=d2.
Proof. intros. rewrite (join_incr_left _ _ _ _ _ J) in JK.
  inv JK; split; trivial.
Qed.

Lemma join_right_agree:
      forall j k b b1 d1 (JK: join j k b = Some(b1,d1))
             b2 d2 (K: k b = Some(b2,d2)) (D:disjoint j k),
      b1=b2 /\ d1=d2.
Proof. intros. rewrite (join_incr_right _ _ D _ _ _ K) in JK.
  inv JK; split; trivial.
Qed.

Lemma join_disjoint: forall f g h (FH: disjoint f h) (GH: disjoint g h),
                     disjoint (join f g) h.
Proof. intros. intros b.
destruct (FH b); try (right; assumption).
destruct (GH b); try (right; assumption).
left. apply joinI_None; assumption.
Qed.

Lemma join_None_rightneutral: forall j, join j (fun b => None) = j.
Proof. unfold join; intros. extensionality b.
  destruct (j b); trivial. destruct p; trivial.
Qed.

Lemma join_None_leftneutral: forall j, join (fun b => None) j = j.
Proof. unfold join; intros. extensionality b. trivial. Qed.

Lemma join_local_extern j L: j = join (local_of j L) (extern_of j L).
Proof. extensionality b. unfold join, local_of, extern_of.
destruct (j b); destruct (L b); simpl; trivial. destruct p; trivial.
Qed.

Lemma compose_meminj_join j1 j2 k1 k2 (D1: disjoint j1 k1) 
   (D3: forall b1 b2 d1, j1 b1 = Some(b2,d1) -> k2 b2 = None)
   (D4: forall b1 b2 d1, k1 b1 = Some(b2,d1) -> j2 b2 = None):
      join (compose_meminj j1 j2) (compose_meminj k1 k2) = 
      compose_meminj (join j1 k1) (join j2 k2).
Proof. extensionality b. unfold compose_meminj, join; specialize (D1 b). 
  remember (j1 b) as q.
  destruct q; symmetry in Heqq.
+ destruct p. destruct D1 as [? | K1]; [ discriminate | rewrite K1]. rename b into b1. rename b0 into b2.
  rewrite (D3 _ _ _ Heqq).
  destruct (j2 b2); trivial.  
  destruct p; trivial.
+ clear D1 D3. rename b into b1. 
  remember (k1 b1) as t. destruct t; trivial. destruct p; symmetry in Heqt.
  rename b into b2. rewrite (D4 _ _ _ Heqt); trivial.
Qed.

Lemma disjoint_local_extern j k L: disjoint (local_of j L) (extern_of k L).
Proof. unfold disjoint, local_of, extern_of. intros b.
destruct (L b). right; trivial. left; trivial. 
Qed.

Definition intern_incr j j' L := 
  inject_incr (local_of j L) (local_of j' L) /\ extern_of j L = extern_of j' L.
Definition extern_incr j j' L := 
  inject_incr (extern_of j L) (extern_of j' L) /\ local_of j L = local_of j' L.

Lemma extern_of_join_local_x j L k: extern_of (join (local_of j L) k) L = extern_of k L.
Proof. extensionality b. unfold extern_of, local_of, join. destruct (L b); trivial. Qed.

Lemma local_of_join_local_x j L k: local_of (join (local_of j L) k) L = join (local_of j L) (local_of k L).
Proof. extensionality b. unfold local_of, join. destruct (L b); trivial. Qed.
(*
Lemma extern_incr_char j k L1 L2
    (HL: forall b1 b2 d, k b1 = Some (b2, d) -> L1 b1 = L2 b2):
     extern_incr j k L1 = mini_extern_incr j k L1 L2.
Proof. unfold extern_incr, mini_extern_incr.
apply prop_ext. split; intros [K1 K2]; split.
+ red; intros. rewrite (join_local_extern j L1) in H. rewrite (join_local_extern k L1).
  rewrite K2 in *; clear K2. apply joinI.
  destruct (joinD_Some _ _ _ _ _ H); clear H. 
  - left; trivial.
  - destruct H0. right. split. trivial. apply K1. trivial.
+ intros. rewrite (join_local_extern j L1) in J. rewrite (join_local_extern k L1) in J'.
  apply joinD_None in J. destruct J.
  destruct (joinD_Some _ _ _ _ _ J'); clear J'.
  - rewrite K2 in *. congruence.
  - destruct H1. destruct (extern_of_ESome _ _ _ _ H2). split; trivial.
    rewrite <- (HL _ _ _ H4); trivial.
+ intros b1 b2 d E. destruct (extern_of_ESome _ _ _ _ E); clear E.
  apply K1 in H0. rewrite extern_of_Ifalse; trivial.
+ extensionality b.
  remember (local_of j L1 b) as q.
  destruct q; symmetry in Heqq.
  - destruct p. destruct (local_of_ESome _ _ _ _ Heqq); clear Heqq.
    apply K1 in H0. symmetry. rewrite local_of_Itrue; trivial.
  - remember (local_of k L1 b) as w.
    destruct w; trivial. destruct p; symmetry in Heqw.
    destruct (local_of_ESome _ _ _ _ Heqw); clear Heqw.
    destruct (local_of_ENone _ _ _ Heqq); [congruence | ].
    destruct (K2 _ _ _ H1 H0); congruence.
Qed.*)

Definition is_extern e L := extern_of e L = e.


Lemma inject_incr_extern_of j L: inject_incr (extern_of j L) j.
Proof. red; intros. apply (extern_of_ESome _ _ _ _ H). Qed.
Lemma inject_incr_local_of j L: inject_incr (local_of j L) j.
Proof. red; intros. apply (local_of_ESome _ _ _ _ H). Qed.

Lemma extern_incr_inject_incr j j' L: extern_incr j j' L -> inject_incr j j'.
Proof.
  intros [A B]. rewrite (join_local_extern j L). rewrite (join_local_extern j' L), B; clear B.
  red; intros. apply joinD_Some in H. apply joinI.
  destruct H as [Q | [Q P]]; [left; trivial | apply A in P; right; split; trivial].
Qed.

(***************** Used for construction of interpolating memories ********************)
Require Import VST.coarse_sepcomp.FiniteMaps. 

Lemma block_content_superbound: forall m,
                                  sigT (fun lo =>
                                          sigT (fun hi =>
                                    forall b ofs,
                                      (ofs<lo \/ ofs>hi)->
                                      ZMap.get ofs ( m.(Mem.mem_contents) !! b) = Undef)).
Proof. intros. destruct (pmap_finite_type _ (Mem.mem_contents m)) as [N property].
  destruct (zmap_finite_type _ (fst (Mem.mem_contents m))) as [lo0 [hi0 property0]].
  cut ( sigT (fun lo =>
                sigT (fun hi =>
                        forall b ofs,
                          (N > b)%positive ->
                          (ofs<lo \/ ofs>hi)->
                          ZMap.get ofs ( m.(Mem.mem_contents) !! b) = Undef) )) .
  { intros X. destruct X as [lo1 [hi1 property1]]. 
    exists (Z.min lo0 lo1); exists (Z.max hi0 hi1).
    intros. destruct (N ?= b)%positive eqn:Nb. 
    + rewrite property, property0.
      rewrite <- (property N). apply m. 
      - xomega. 
      - destruct H; xomega. 
      - intros HH. rewrite Nb in HH; inversion HH.
    + rewrite property, property0.
      rewrite <- (property N). apply m. 
      - xomega. 
      - destruct H; xomega. 
      - intros HH. rewrite Nb in HH; inversion HH.
    + apply property1; trivial. destruct H; xomega. }
  { generalize N. clear N property property0 lo0 hi0.
    specialize (well_founded_induction_type  (Plt_wf)). intros HH.
    apply (HH (fun N : positive =>
          {lo : Z &
          {hi : Z &
          forall (b : positive) (ofs : Z),
          (N > b)%positive ->
          ofs < lo \/ ofs > hi ->
          ZMap.get ofs (Mem.mem_contents m) !! b = Undef}})); intros.
    destruct (x ?= 1)%positive eqn:X.
    + apply Pos.compare_eq_iff in X.
      subst x. exists 1, 1; intros. contradict H0. xomega. 
    + contradict X. apply Pos.nlt_1_r.
    + (*Inductive step*)
      destruct (H (Pos.pred x)) as [lo0 [hi0 property0]]. apply Ppred_Plt. intros Xeq. 
      rewrite <- Pos.compare_eq_iff in Xeq. congruence.
      destruct (zmap_finite_type _ (Mem.mem_contents m) !! (Pos.pred x)) as [lo1 [hi1 property1]].
      exists (Z.min lo0 lo1), (Z.max hi0 hi1).
      intros. 
      destruct (Pos.pred x ?= b)%positive eqn:xb.
      - rewrite Pos.compare_eq_iff in xb; subst b.
        rewrite property1. apply m.
        destruct H1; xomega.
      - cut False; try contradiction ; clear - X xb H0. 
        apply Pos.succ_lt_mono in xb. 
        apply Pos.lt_succ_r in xb.
        rewrite Pos.succ_pred in xb. xomega.
        xomega.
      - apply property0. exact xb.
        destruct H1; xomega. }
Qed.

Lemma delta_superbound: forall (j:meminj) N,
                          sigT ( fun lod =>
                                   sigT (fun hid =>
                                    forall b,
                                      forall b' d, 
                                        (b < N)%positive ->
                                        j b = Some (b', d) ->
                                                   d < hid /\ d > lod)).
  intros j.
  specialize (well_founded_induction_type  (Plt_wf)). intros HH.
  apply (HH (fun N : positive =>
         {lod : Z &
         {hid : Z &
          forall (b : positive) (b' : block) (d : Z),
          (b < N)%positive -> j b = Some (b', d) -> d < hid /\ d > lod}})); intros.
  destruct (peq x 1).
  + exists 1, 1; intros. subst x. contradict H0; xomega.
  + destruct (H (x-1)%positive) as [lo [hi property]].
    { apply Ppred_Plt in n; xomega. }
    { destruct (j (x-1)%positive) eqn:jmap; try destruct p as [b' d].
      - exists (Z.min lo (d - 1)), (Z.max hi (d + 1)); intros.
        destruct (b ?= (x - 1))%positive eqn:bx.
        * apply Pos.compare_eq_iff in bx; subst b. 
          rewrite jmap in H1; inversion H1. xomega.
        * apply (property _ _ _ bx) in H1. xomega.
        * rewrite Pcompare_eq_Gt in bx. rewrite Pos.gt_lt_iff in bx.
          apply Pos.succ_lt_mono in bx. 
          apply Pos.lt_succ_r in bx.
          rewrite Pplus_one_succ_r, Pos.sub_add in bx; xomega.
      - exists lo, hi; intros.
        eapply property; eauto.
        destruct (b ?= (x - 1))%positive eqn:bx.
        * apply Pos.compare_eq_iff in bx; subst b. congruence.
        * trivial.
        * rewrite Pcompare_eq_Gt in bx. rewrite Pos.gt_lt_iff in bx.
          apply Pos.succ_lt_mono in bx. 
          apply Pos.lt_succ_r in bx.
          rewrite Pplus_one_succ_r, Pos.sub_add in bx; xomega. }
 Qed.
