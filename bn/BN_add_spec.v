
Definition chunk_add (a b c:Chunk) : Chunk * Chunk :=
  let x := Int.unsigned a + Int.unsigned b + Int.unsigned c
  in (Int.repr (x mod Int.modulus), Int.add_carry a b c).

Definition chunk_add_noCarry (a b: Chunk): Chunk * Chunk :=
      let x := Int.unsigned a + Int.unsigned b
      in if zlt x Int.modulus then (Int.repr x, Int.zero) 
         else (Int.repr (x mod Int.modulus), Int.one).
      
Lemma chunk_add_noCarry_sound a b: 
      chunk_add a b Int.zero = chunk_add_noCarry a b.
Proof. intros.
  unfold chunk_add, chunk_add_noCarry, Int.add_carry. rewrite Zplus_0_r.
   remember (zlt (Int.unsigned a + Int.unsigned b) Int.modulus).
   destruct s; clear Heqs; trivial.
   rewrite Zmod_small; trivial. 
   split; trivial.
   specialize (Int.unsigned_range a). 
   specialize (Int.unsigned_range b). intros. omega.
Qed.
  
Definition chunk_add_Carry (a b: Chunk): Chunk * Chunk :=
      let x := Int.unsigned a + Int.unsigned b + Int.unsigned Int.one
      in if zlt x Int.modulus then (Int.repr x, Int.zero) 
         else (Int.repr (x mod Int.modulus), Int.one).
      
Lemma chunk_add_Carry_sound a b: 
      chunk_add a b Int.one = chunk_add_Carry a b.
Proof. intros.
  unfold chunk_add, chunk_add_Carry, Int.add_carry. simpl.
   remember (zlt (Int.unsigned a + Int.unsigned b + Int.unsigned Int.one) Int.modulus).
   destruct s; clear Heqs; trivial.
   rewrite Zmod_small; trivial. 
   split; trivial.
   specialize (Int.unsigned_range a). 
   specialize (Int.unsigned_range b). 
   specialize (Int.unsigned_range Int.one). intros. omega.
Qed.
  
Definition chunk_add' (a b c:Chunk) : Chunk * Chunk :=
  let x := Int.unsigned a + Int.unsigned b + Int.unsigned c
  in if zlt x Int.modulus then (Int.repr x, Int.zero) 
         else (Int.repr (x mod Int.modulus), Int.one).

Lemma chunk_add_chunk_add' a b c: chunk_add a b c = chunk_add' a b c.
Proof. intros.
  unfold chunk_add, chunk_add', Int.add_carry.
   remember (zlt (Int.unsigned a + Int.unsigned b+ Int.unsigned c) Int.modulus).
   destruct s; clear Heqs; trivial.
   rewrite Zmod_small; trivial. 
   split; trivial.
   specialize (Int.unsigned_range a). 
   specialize (Int.unsigned_range b). 
   specialize (Int.unsigned_range c). intros. omega.
Qed.

Lemma chunk_add_sound a b c res carry
      (ADD:chunk_add a b c =(res,carry))
      (HC: c= Int.zero \/ c=Int.one):
  (carry = Int.zero \/ carry =Int.one) /\
  ch2Z a + ch2Z b + ch2Z c = ch2Z res + Int.unsigned carry * Int.modulus.
Proof. intros.
  unfold chunk_add in ADD. inv ADD.
  unfold ch2Z. rewrite Int.unsigned_repr.
  Focus 2.
    remember (Int.unsigned a + Int.unsigned b + Int.unsigned c) as d.
    specialize (Z_mod_lt d Int.modulus Int.modulus_pos).
    specialize (Int.unsigned_range a). 
    specialize (Int.unsigned_range b). 
    specialize (Int.unsigned_range c). intros. remember (d mod Int.modulus).
    rewrite <- initialize.max_unsigned_modulus  in H2. omega.
  remember (Int.unsigned a + Int.unsigned b + Int.unsigned c) as d.
    specialize (Int.unsigned_range a). 
    specialize (Int.unsigned_range b). 
    specialize (Int.unsigned_range c). intros.
  unfold Int.add_carry. rewrite <- Heqd.
  destruct (zlt d Int.modulus).
    split. left; trivial.
    rewrite Z.mod_small.
    unfold Int.zero. simpl. omega. omega.
  split. right; trivial.
  assert (M: d / Int.modulus = 1).
    eapply Zdiv_unique.
    instantiate (1:= d-Int.modulus). omega.
    split. omega. 
    apply Z.lt_sub_lt_add_r. subst d.
    destruct HC; subst. unfold Int.zero; rewrite Zplus_0_r. omega.
    unfold Int.one. rewrite Int.unsigned_repr. omega.  
    rewrite int_max_unsigned_eq. omega.
  specialize (Z_div_mod_eq d Int.modulus Int.modulus_pos).
    rewrite Zmult_comm, Z.add_comm, M. trivial.
Qed. 

Function chunks_add (ab: list (Chunk * Chunk)) (c:Chunk): list Chunk :=
  match ab with
    nil => normalize [c]
  | (a1,b1)::t =>
        match chunk_add a1 b1 c with
          (d, x) => d :: (chunks_add t x)
        end
  end.


Lemma chunks_add_cons' h t c: 
      chunks_add (h::t) c =
        match chunk_add (fst h) (snd h) c with
          (d, x) => d :: (chunks_add t x)
        end.
Proof. unfold chunk_add. destruct h. reflexivity. Qed.

Lemma chunks_add_cons a b t c: 
      chunks_add ((a,b)::t) c =
        match chunk_add a b c with
          (d, x) => d :: (chunks_add t x)
        end.
Proof. reflexivity. Qed.

Lemma chunks_add_sound: forall ab a b (SP: split ab = (a, b)) c
      (HC: c= Int.zero \/ c=Int.one), 
      chunks2Z (chunks_add ab c) = chunks2Z a + chunks2Z b + ch2Z c.
Proof.
  induction ab.
    simpl; intros. inv SP; simpl. 
    unfold normalize; simpl. 
    remember (Int.eq c Int.zero) as b; destruct b; simpl; trivial.
    apply eq_sym in Heqb. apply int_eq_e in Heqb. subst c. trivial. 
  intros aS bS SP. simpl in SP. destruct a. remember (split ab) as sp. destruct sp.
    inv SP. rename l into aT. rename l0 into bT.
    specialize (IHab _ _ (eq_refl _)).
    intros. unfold chunks2Z. rewrite chunks_add_cons. fold chunks2Z.
    remember (chunk_add c c0 c1) as X; symmetry in HeqX. destruct X.
    destruct (chunk_add_sound _ _ _ _ _ HeqX HC); clear HeqX HC.
    rewrite chunks2Z_cons. rewrite IHab; clear IHab; trivial.
    repeat rewrite Z.mul_add_distr_l. repeat rewrite Z.add_assoc.
    repeat rewrite <- Zplus_assoc.
    f_equal.
    rewrite <- (Zplus_comm (ch2Z c0 + ch2Z c1)).
    repeat rewrite Zplus_assoc. rewrite H0; clear H0. 
    assert (Int.modulus = 2^32) by reflexivity.
    rewrite H0. unfold ch2Z. rewrite (Zmult_comm (Int.unsigned c3)). omega.
Qed. 

Lemma length_chunks_add: forall l c, (length l <= length (chunks_add l c) <= length l + 1)%nat.
Proof.
  induction l; simpl. unfold normalize; simpl. intros.
  destruct (Int.eq c Int.zero); simpl. omega. omega.
destruct a. simpl; intros. specialize (IHl (Int.add_carry c c0 c1)). omega.
Qed.

Function chunks_add' (a b: list Chunk): list Chunk := chunks_add (Combine a b) zeroChunk.

Lemma chunks_add'_sound a b: chunks2Z (chunks_add' a b) = chunks2Z a + chunks2Z b.
Proof.
  unfold chunks_add'. 
  remember (max (length a) (length b)) as mx.
  rewrite (chunks_add_sound _ (chunks_zero_extend a mx) (chunks_zero_extend b mx)).
    repeat rewrite chunks2Z_zero_extend. rewrite zeroChunk0, Zplus_0_r; trivial.
  rewrite Combine_split. subst; trivial.
  left; reflexivity.
Qed.

Lemma length_chunks_add' a b: 
  (max (length a) (length b) <= length (chunks_add' a b) <= max (length a) (length b) + 1)%nat.
Proof. unfold chunks_add'.
  specialize (length_chunks_add (Combine a b) zeroChunk). intros.
  rewrite length_Combine in *. apply H.
Qed.

(*Choice of dmax:=dmaxA and flags:=flagsA arbitrary for now*)
Definition bn_add (a b : bnabs) : bnabs :=
  match a, b with
   BNabs dA topA dmaxA negA flagsA,
   BNabs dB topB dmaxB negB flagsB
  => match negA, negB with
       true, true => let mrg := merge_chunks (firstn topA dA) (firstn topB dB)
                     in let d := chunks_add mrg Int.zero
                     in BNabs d (length d) dmaxA true flagsA
     | true, false => let mrg := merge_chunks (firstn topB dB) (firstn topA dA)
                     in let d := chunks_sub mrg Int.zero
                     in let cmp := match chunks_cmp mrg with Lt => true | _ => false end
                     in BNabs d (length d) dmaxA cmp flagsA
     | false, true => let mrg := merge_chunks (firstn topB dA) (firstn topA dB)
                     in let d := chunks_sub mrg Int.zero
                     in let cmp := match chunks_cmp mrg with Lt => true | _ => false end
                     in BNabs d (length d) dmaxA cmp flagsA
     | false, false => let mrg := merge_chunks (firstn topA dA) (firstn topB dB)
                     in let d := chunks_add mrg Int.zero
                     in BNabs d (length d) dmaxA false flagsA
    end
  end.


Lemma bn_add_sound a b (SIGN: bn_neg a = bn_neg b):
      bn2Z (bn_add a b) = bn2Z a + bn2Z b.
Proof. unfold bn_add.
  destruct a as [dA topA dmaxA negA flagsA].
  destruct b as [dB topB dmaxB negB flagsB].
  simpl in *. subst.
  destruct negB.
  { (*both negative *) simpl.
    rewrite firstn_same. 2: omega.
    unfold merge_chunks.
    destruct (Max.max_spec (length (firstn topA dA)) (length (firstn topB dB))) 
      as [[H HH] | [H HH]]; rewrite HH; clear H.
    { erewrite chunks_add_sound; auto.
       Focus 2. apply combine_split. do 2 rewrite length_chunks_zero_extend.
                rewrite HH, Max.max_idempotent. trivial.
       do 2 rewrite chunks2Z_zero_extend. rewrite ch2Z_zero, Zplus_0_r; trivial. omega. }
    { erewrite chunks_add_sound; auto.
       Focus 2. apply combine_split. do 2 rewrite length_chunks_zero_extend.
                rewrite Max.max_comm in HH. rewrite HH, Max.max_idempotent. trivial.
       do 2 rewrite chunks2Z_zero_extend. rewrite ch2Z_zero, Zplus_0_r; trivial. omega. }
   }
  { (*both positive *) simpl.
    rewrite firstn_same. 2: omega.
    unfold merge_chunks.
    destruct (Max.max_spec (length (firstn topA dA)) (length (firstn topB dB))) 
      as [[H HH] | [H HH]]; rewrite HH; clear H.
    { erewrite chunks_add_sound; auto.
      Focus 2. apply combine_split. do 2 rewrite length_chunks_zero_extend.
               rewrite HH, Max.max_idempotent. trivial.
      do 2 rewrite chunks2Z_zero_extend. rewrite ch2Z_zero, Zplus_0_r; trivial. }
    { erewrite chunks_add_sound; auto.
      Focus 2. apply combine_split. do 2 rewrite length_chunks_zero_extend.
               rewrite Max.max_comm in HH. rewrite HH, Max.max_idempotent. trivial.
      do 2 rewrite chunks2Z_zero_extend. rewrite ch2Z_zero, Zplus_0_r; trivial. }
  }
Qed.

Definition bn_add' (a b : bnabs) : bnabs :=
  match a, b with
   BNabs dA topA dmaxA negA flagsA,
   BNabs dB topB dmaxB negB flagsB
  => let mrg := merge_chunks (firstn topA dA) (firstn topB dB)
     in let d := chunks_add mrg Int.zero
     in BNabs d (length d) dmaxA true flagsA
  end.
Lemma bn_add_sound_neg a b (A:~bn_nonneg a) (B: ~bn_nonneg b):
      bn2Z (bn_add' a b) = bn2Z a + bn2Z b.
Proof. unfold bn_add'.
  destruct a as [dA topA dmaxA negA flagsA].
  destruct b as [dB topB dmaxB negB flagsB].
  simpl in *. destruct negA. 2: elim A; trivial. destruct negB. 2: elim B; trivial.
  rewrite firstn_same. 2: omega.
  unfold merge_chunks.
  destruct (Max.max_spec (length (firstn topA dA)) (length (firstn topB dB))) 
    as [[H HH] | [H HH]]; rewrite HH; clear H.
  { erewrite chunks_add_sound; auto.
     Focus 2. apply combine_split. do 2 rewrite length_chunks_zero_extend.
              rewrite HH, Max.max_idempotent. trivial.
     do 2 rewrite chunks2Z_zero_extend. rewrite ch2Z_zero, Zplus_0_r; trivial. omega. }
  { erewrite chunks_add_sound; auto.
     Focus 2. apply combine_split. do 2 rewrite length_chunks_zero_extend.
              rewrite Max.max_comm in HH. rewrite HH, Max.max_idempotent. trivial.
     do 2 rewrite chunks2Z_zero_extend. rewrite ch2Z_zero, Zplus_0_r; trivial. omega. }
Qed.
   
