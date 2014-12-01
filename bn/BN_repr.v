Require Import floyd.proofauto.
Require Import Coqlib.
Require Import Integers.
Require Import List. Import ListNotations.
(*Local Open Scope logic.*)

Require Import sha.pure_lemmas.
Require Import sha.common_lemmas.

Require Import bn.minibn.
Local Open Scope logic.

Lemma skipn_add {A}: forall t n (ch:list A),
      skipn (t+n) ch = skipn n (skipn t ch).
Proof.
  induction t; simpl. trivial.
  intros. destruct ch. 
    rewrite skipn_nil; trivial. 
  rewrite IHt; trivial.
Qed.

Lemma firstn_app1 {A}: forall n (l t:list A),
   (n >= length l)%nat -> firstn n (l++t) = l ++ firstn (n-length l) t.
Proof. intros n; induction n; simpl; intros.
  destruct l; simpl in *; trivial. omega.
  destruct l; simpl in *. trivial. rewrite IHn. trivial. omega.
Qed.

Lemma firstn_nil {A}: forall m, firstn m (nil:list A) = (nil:list A).
Proof. intros. rewrite firstn_same. trivial. simpl. omega. Qed.

Lemma skipn_all {A}: forall l, skipn (length l) l = (nil:list A).
Proof. intros l.
  induction l; simpl; trivial.
Qed.
Lemma skipn_all' {A}: forall n l, (n>=length l)%nat -> skipn n l = (nil:list A).
Proof. intros n.
  induction n; simpl; trivial. intros. destruct l; simpl in *; trivial. omega. 
  intros. destruct l; simpl in *; trivial. apply IHn. omega.
Qed.

Lemma firstn_list_repeat1 {A} k n (x:A) (N: (n>=k)%nat):
      firstn n (list_repeat k x) = list_repeat k x.
Proof.
  intros. specialize (firstn_app1 n (list_repeat k x) nil).
  rewrite app_nil_r. intros. rewrite H. 
   rewrite firstn_nil. apply app_nil_r.
  rewrite length_list_repeat. apply N. 
Qed.

Lemma firstn_list_repeat2 {A}: forall k n (x:A) (N: (n<=k)%nat),
      firstn n (list_repeat k x) = list_repeat n x.
Proof.
  intros k.
  induction k. simpl. intros. destruct n; simpl. trivial. omega.
  simpl; intros. destruct n; simpl in *.  trivial.
  rewrite IHk. trivial. omega. 
Qed.

Lemma firstn_geq {A}: forall k (l:list A),
    (k>=length l)%nat ->  firstn k l = l.
Proof. 
  induction k; simpl; intros. destruct l; trivial. simpl in *; omega.
destruct l. trivial. f_equal. apply IHk. simpl in *; omega.
Qed.

Lemma rev_list_repeat {A} (a:A): forall n, rev (list_repeat n a) = list_repeat n a.
Proof. induction n; simpl; trivial. rewrite IHn; clear IHn.
specialize (list_repeat_app A); intros Q.
rewrite (Q n (1%nat)).
specialize (Q (1%nat) n). rewrite plus_comm in Q. simpl in Q. rewrite Q; trivial.
Qed.  

Definition Chunk:Type := int.
Function ch2Z (c:Chunk):Z:= Int.unsigned c.

Lemma ch2Z_zero: ch2Z Int.zero = 0. Proof. reflexivity. Qed.
Lemma ch2Z_one: ch2Z Int.one = 1. Proof. reflexivity. Qed.

Function chunks2Z (l:list Chunk) : Z :=
  match l with 
   nil => 0
 | cons c t => 2^32 * (chunks2Z t) + ch2Z c end.

Lemma chunks2Z_cons c t: chunks2Z (cons c t) = 2^32 * (chunks2Z t) + ch2Z c.
Proof. reflexivity. Qed.
(*
Definition bn_z (b:bnabs) (z:Z) : Prop :=
  match b with BNabs d top dmax neg flags =>
    length d = top /\ 
    z = if neg then - (chunks2Z d) else chunks2Z d
  end.*)
Definition zeroChunk: Chunk := Int.zero.

Lemma zeroChunk0: ch2Z zeroChunk = 0. Proof. reflexivity. Qed.

Definition chunks_zero_extend (d:list Chunk) n := d ++ (list_repeat (minus n (length d)) zeroChunk).

Lemma zeroChunks: forall n, chunks2Z (list_repeat n zeroChunk) = 0.
Proof. intros n. 
  induction n; simpl. trivial.
  rewrite IHn. try rewrite zeroChunk0. trivial.
Qed.

Lemma chunk2Z_zero n: forall ch, chunks2Z (ch ++ list_repeat n zeroChunk) = chunks2Z ch.
Proof. intros ch.
  induction ch. simpl. apply zeroChunks.
  rewrite <- app_comm_cons.
  simpl. rewrite IHch; trivial.
Qed.

Lemma chunks2Z_zero_extend d n: chunks2Z (chunks_zero_extend d n) = chunks2Z d.
Proof. intros. apply chunk2Z_zero. Qed.

Function normalize_aux (l:list Chunk):list Chunk :=
  match l with 
    nil => nil
  | cons x t => if Int.eq x Int.zero then normalize_aux t else l
  end.

Lemma extend_normalize_aux: forall l, exists n,
  (list_repeat n zeroChunk) ++ (normalize_aux l) = l.
Proof. induction l; simpl; intros. exists O; simpl; trivial.
  destruct IHl as [n Hn].
  remember (Int.eq a Int.zero) as b; destruct b; simpl. 
    apply eq_sym in Heqb. apply int_eq_e in Heqb. subst a.
    exists (S n); simpl. rewrite Hn; clear Hn. trivial.
  exists O; trivial.
Qed.  

Lemma normalize_aux_idempotent: forall l, normalize_aux (normalize_aux l) = normalize_aux l.
Proof. induction l; simpl; intros; trivial.
  remember (Int.eq a Int.zero) as d. 
  destruct d; simpl; trivial.
  rewrite <- Heqd; trivial.
Qed.

Function normalize l := rev (normalize_aux (rev l)).

Lemma normalize_extend: forall l, exists n,
  (normalize l) ++ (list_repeat n zeroChunk) = l.
Proof. intros. unfold normalize. 
  destruct (extend_normalize_aux (rev l)) as [n m]. 
  assert (R: rev (list_repeat n zeroChunk ++ normalize_aux (rev l)) = rev(rev l)).
    rewrite m; trivial.
  clear m. rewrite rev_app_distr, rev_list_repeat, rev_involutive in R.
  exists n; trivial.
Qed. 

Lemma normalize_sound l: chunks2Z (normalize l) = chunks2Z l.
Proof. destruct (normalize_extend l) as [n Hn].
  rewrite <- Hn at 2.
  apply eq_sym. apply chunk2Z_zero.
Qed.

Lemma normalize_idempotent l: normalize (normalize l) = normalize l.
Proof. unfold normalize.
  rewrite rev_involutive, normalize_aux_idempotent. trivial.
Qed.

Function Combine (a b: list Chunk): list (Chunk * Chunk) := 
  let mx := max (length a) (length b)
  in combine (chunks_zero_extend a mx) (chunks_zero_extend b mx).

Lemma chunks_zero_extend_length l n: length (chunks_zero_extend l n) = max (length l) n.
Proof. unfold chunks_zero_extend.
  rewrite app_length, length_list_repeat. remember (length l) as d; clear Heqd.
  destruct (le_lt_dec d n).
    rewrite Max.max_r; trivial. omega.
  rewrite max_l; omega.
Qed.

Lemma length_Combine: forall a b, length (Combine a b) = max (length a) (length b).
Proof. unfold Combine. intros.
  rewrite combine_length.
  repeat rewrite chunks_zero_extend_length.
  rewrite Max.max_assoc; rewrite Max.max_idempotent.
  rewrite (Max.max_comm (length b)).
  rewrite <- Max.max_assoc; rewrite Max.max_idempotent.
  apply Min.min_idempotent.
Qed.

Lemma Combine_split a b:
  let mx := max (length a) (length b) in
  split (Combine a b) = (chunks_zero_extend a mx, chunks_zero_extend b mx).
Proof. 
  apply combine_split.
    repeat rewrite chunks_zero_extend_length. 
  destruct (Max.max_dec (length a) (length b)); rewrite e.
  rewrite Max.max_idempotent, Max.max_comm, e. trivial.
    rewrite e, Max.max_idempotent; trivial.
Qed.

Lemma chunks2Z_nonneg: forall l, 0 <= chunks2Z l.
Proof. induction l. simpl. omega.
  rewrite chunks2Z_cons. unfold ch2Z. specialize (Int.unsigned_range a). intros. 
  assert (2 ^ 32 = Int.modulus) by reflexivity. rewrite H0. 
  apply Z.add_nonneg_nonneg. 2: apply H.
  apply Z.mul_nonneg_nonneg; trivial.
Qed. 

Lemma zadd_zero_nonneg p q: 0 = p + q -> 0 <=p -> q>= 0 -> p=0 /\ q=0.
Proof. omega. Qed.

Lemma chunks2Z_0: forall l, 0 = chunks2Z l -> l = list_repeat (length l) Int.zero.
Proof. induction l. simpl. trivial.
  rewrite chunks2Z_cons. unfold ch2Z. specialize (Int.unsigned_range a). intros. 
  assert (2 ^ 32 = Int.modulus) by reflexivity. rewrite H1 in *.
  specialize Int.modulus_pos.
  apply zadd_zero_nonneg in H0.
  Focus 2.
    apply Z.mul_nonneg_nonneg. omega. apply chunks2Z_nonneg.
  2: omega. 
  destruct H0 as [X Y]. 
  apply Zmult_integral in X. destruct X. intros. omega.
  intros. simpl. rewrite <- IHl. 2: rewrite H0; trivial.
  f_equal. assert (Int.repr (Int.unsigned a) = Int.repr 0). rewrite Y; trivial.
  rewrite Int.repr_unsigned in H3. apply H3.
Qed.

Lemma normalize_aux_cons_zero: forall l, normalize_aux (Int.zero :: l) = normalize_aux l.
Proof. unfold normalize_aux. intros. rewrite Int.eq_true. trivial. Qed.

Lemma normalize_snoc_zero: forall l, normalize (l ++ [Int.zero]) = normalize l.
Proof. unfold normalize. intros. rewrite rev_app_distr. simpl. trivial. Qed.

Lemma list_nil_length {A} (l:list A): l= [] -> (length l <= 0)%nat.
Proof. intros. subst. trivial. Qed.

(*Lemma rev_list_repeat {A} (c:A): forall n, rev (list_repeat n c) = list_repeat n c.*)

Lemma normalize_aux_zerolist: forall k, normalize_aux (list_repeat k Int.zero) = [].
Proof. induction k; simpl; trivial. Qed.

Lemma normalize_zerolist: forall k, normalize (list_repeat k Int.zero) = [].
Proof. unfold normalize. intros. rewrite rev_list_repeat, normalize_aux_zerolist. trivial. Qed.

Lemma length_chunks_zero_extend l n: length (chunks_zero_extend l n) = max (length l) n.
Proof. intros.
  unfold chunks_zero_extend.
  rewrite app_length. rewrite length_list_repeat.
  destruct (Max.max_spec (length l) n) as [[A B] | [A B]]; rewrite B; omega. 
Qed.

Lemma length_normalize: forall l n (HL: chunks2Z l < Int.modulus ^ (Z.of_nat n)), (length (normalize l) <= n)%nat.
Proof.
  induction l; intros.
    simpl. omega.
  rewrite chunks2Z_cons in HL.
  destruct n.
    assert (N: Z.of_nat 0 = Z0) by reflexivity.
    rewrite N, Z.pow_0_r in HL.
    specialize (Int.unsigned_range a). intros. unfold ch2Z in HL. clear IHl N.
    destruct l.
      simpl in *.
      unfold normalize. simpl. remember (Int.eq a Int.zero) as d.
      destruct d. simpl. trivial. specialize (Int.eq_spec a Int.zero). rewrite <- Heqd. intros.
        exfalso. clear Heqd. destruct H as [? _]. apply H0; clear H0.
        apply Z_le_lt_eq_dec in H. destruct H.  omega. unfold Int.zero. rewrite e; clear e.
        rewrite Int.repr_unsigned. trivial.
    assert (0 <= 2 ^ 32 * chunks2Z (c :: l)).
      apply Z.mul_nonneg_nonneg. 
         assert (2 ^ 32 = Int.modulus) by reflexivity. rewrite H0. specialize Int.modulus_pos. omega. 
      apply chunks2Z_nonneg.
    apply Z_le_lt_eq_dec in H0. destruct H0. remember (2 ^ 32 * chunks2Z (c :: l))%Z. clear Heqz. exfalso. omega.
    rewrite <- e in *. simpl in HL. 
      destruct H. 
      apply Z_le_lt_eq_dec in H. destruct H. clear - HL l0. exfalso. omega.
      rewrite <- e0 in *. 
      assert (Int.repr 0 = Int.repr (Int.unsigned a)). rewrite <- e0; trivial.
      rewrite Int.repr_unsigned in H. subst a.
      symmetry in e. apply Zmult_integral in e.
      destruct e. exfalso.  clear -H. assert (2 ^ 32 = Int.modulus) by reflexivity. rewrite H0 in *. specialize Int.modulus_pos. omega.
      symmetry in H. apply chunks2Z_0 in H. rewrite H. clear H e0 H0 HL.
      apply list_nil_length. simpl.
      Lemma norm_triv l l' ll: l'=l -> normalize l' = ll -> normalize l = ll.
        Proof. intros; subst. trivial. Qed.
      eapply norm_triv. instantiate (1:= list_repeat (S(length (c :: l))) Int.zero). reflexivity.
      apply normalize_zerolist.
     assert (2 ^ 32 * chunks2Z l < Int.modulus ^ Z.of_nat (S n)).
       clear IHl. unfold ch2Z in HL.
       eapply Z.le_lt_trans; try eassumption.
       specialize (Int.unsigned_range a); intros. omega.
     clear HL. 
     assert (M: 2 ^ 32 = Int.modulus) by reflexivity. rewrite M in *. clear M. 
     assert (chunks2Z l < Int.modulus ^ Z.of_nat n).
       rewrite Nat2Z.inj_succ, Z.pow_succ_r in H.
       eapply Zmult_gt_0_lt_reg_r. apply Int.modulus_pos. 
         rewrite Z.mul_comm. rewrite (Z.mul_comm (Int.modulus ^ Z.of_nat n)). trivial. 
       apply Zle_0_nat.
     clear H. 
      specialize (IHl _ H0). clear H0.
      unfold normalize in *. rewrite rev_length in *. simpl. remember (rev l). clear Heql0.
      clear l. generalize dependent n.
      induction l0; simpl; intros. destruct (Int.eq a Int.zero); simpl. omega. omega.
      destruct (Int.eq a0 Int.zero). apply IHl0. trivial.
      rewrite app_comm_cons, app_length. clear - IHl. simpl in *. omega.
 Qed. 


Inductive bnabs :=
 BNabs: forall (chunks: list Chunk) 
               (top dmax:nat) (neg:bool) (flags: int), 
               bnabs.

Definition bn_chunks (b:bnabs):list Chunk :=
  match b with BNabs ch _ _ _ _  => ch end.

Definition bn2Z (b:bnabs):Z :=
  match b with BNabs d top dmax neg flags =>
    if neg then - (chunks2Z (firstn top d)) else chunks2Z (firstn top d)
  end.

Definition bn_zero_extend (b:bnabs) n: bnabs :=
  match b with BNabs d top dmax neg flags =>
    BNabs (d ++ (list_repeat (minus n top) zeroChunk))
             (max n top) dmax neg flags
  end.

Definition top_precise (b:bnabs) :=
  match b with BNabs d top dmax neg flags => top = length d end.

Definition top_ok (b:bnabs) :=
  match b with BNabs d top dmax neg flags => (top >= length d)%nat end.

Lemma top_precise_ok b: top_precise b -> top_ok b.
Proof. destruct b; simpl. omega. Qed.

Lemma bn2Z_zero_extend_ok b n (TP: top_ok b):
      bn2Z (bn_zero_extend b n) =  bn2Z b.
Proof.
  destruct b. simpl in*; intros.
  cut (chunks2Z (firstn (max n top) (chunks ++ list_repeat (n - top) zeroChunk))
        = chunks2Z (firstn top chunks)).
  intros CH; rewrite CH; trivial.
  destruct (le_dec top n). 
  Focus 2. rewrite (not_le_minus_0 _ _ n0), Max.max_r, app_nil_r. trivial. omega.
  rewrite Max.max_l. 2: trivial.
    rewrite firstn_app1. 2: omega.
    rewrite firstn_list_repeat1. Focus 2. omega. 
   rewrite firstn_geq; trivial.
   apply chunk2Z_zero.
Qed.

Lemma bn2Z_zero_extend_precise b n (TP: top_precise b):
      bn2Z (bn_zero_extend b n) =  bn2Z b.
Proof. apply top_precise_ok in TP.
  apply bn2Z_zero_extend_ok; trivial.
Qed.

Definition bn_zero : bnabs := BNabs [Int.zero] 1 4 false Int.zero.
Lemma bn_zeroO: bn2Z bn_zero = 0. Proof. reflexivity. Qed.

Definition bn_one : bnabs := BNabs [Int.one] 1 4 false Int.zero.
Lemma bn_one1: bn2Z bn_one = 1. Proof. reflexivity. Qed.

Definition bn_neg b := match b with BNabs d top dmax neg flags => neg end.
Check data_at. Eval compute in (reptype t_struct_bignum_st).
Definition bnstate: Type := 
  (val * (val * (val * (val * val))))%type.
(* d (top (dmax (neg flags)))*)
(*
Definition chunks_relate (d: list Chunk) (d': val):mpred := 
   array_at tuint Tsh (ZnthV tuint (map Vint d)) Z0 (Zlength d) d'.*)
(*Eval compute in (reptype (tarray tuint (Zlength d))).*)
Definition chunks_relate (d: list Chunk) (d': val):mpred := 
   data_at Tsh (tarray tuint (Zlength d)) (map Vint d) d'.
 
Definition tops_relate (t:nat) (t':val):Prop := t' = Vint (Int.repr (Z.of_nat t)).

Definition negs_relate (n:bool) (n':val):Prop := 
  if n then n' = Vint Int.one else exists z, z<>Int.one /\ n'=Vint z.
            
Definition bn_relate (b: bnabs) (r: bnstate) : mpred :=
  match b, r with BNabs d t dm n f,
     (d' ,(t' ,(dm', (n', f'))))  =>
    chunks_relate d d' &&
    !! (tops_relate t t' /\ negs_relate n n' /\ t = length d /\ 
        (t <= dm)%nat /\ dm'=Vint (Int.repr (Z.of_nat dm)))
    (*no condition for flags (yet*)
  end.

Definition bnstate_ (b: bnabs) (c: val) : mpred :=
   EX r:bnstate, 
     bn_relate b r * data_at Tsh t_struct_bignum_st r c.
