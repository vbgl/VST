
Definition chunk_sub (a b c:Chunk) : Chunk * Chunk :=
  let x := Int.unsigned a - Int.unsigned b - Int.unsigned c
  in if zle 0 x then (Int.repr (x mod Int.modulus), Int.zero)
  else (Int.repr (x mod Int.modulus), Int.one).

Definition chunk_sub_noCarry (a b: Chunk): Chunk * Chunk :=
      let x := Int.unsigned a - Int.unsigned b
      in if zle 0 x then (Int.repr (x mod Int.modulus), Int.zero)
         else (Int.repr (x mod Int.modulus), Int.one).
      
Lemma chunk_sub_noCarry_sound a b: 
      chunk_sub a b Int.zero = chunk_sub_noCarry a b.
Proof. intros.
  unfold chunk_sub, chunk_sub_noCarry; rewrite Zminus_0_r.
   remember (zle 0 (Int.unsigned a - Int.unsigned b)).
   destruct s; clear Heqs; trivial.
Qed.
  
Definition chunk_sub_Carry (a b: Chunk): Chunk * Chunk :=
      let x := Int.unsigned a - Int.unsigned b - Int.unsigned Int.one
      in if zle 0 x then (Int.repr x, Int.zero) 
         else (Int.repr (x mod Int.modulus), Int.one).
      
Lemma chunk_sub_Carry_sound a b: 
      chunk_sub a b Int.one = chunk_sub_Carry a b.
Proof. intros.
  unfold chunk_sub, chunk_sub_Carry.
   remember (zle 0 (Int.unsigned a - Int.unsigned b - Int.unsigned Int.one)).
   destruct s; clear Heqs; trivial. f_equal.
   rewrite Zmod_small; trivial. 
   split; trivial.
   specialize (Int.unsigned_range a). 
   specialize (Int.unsigned_range b).
   specialize (Int.unsigned_range Int.one). intros. omega.
Qed.
(*
Lemma chunk_sub_sound_noCarry a b res c:
  chunk_sub a b Int.zero = (res,c) ->
    (ch2Z a - ch2Z b) + ch2Z c * Int.modulus = ch2Z res.
Proof. unfold chunk_sub; simpl; intros. 
  rewrite Zminus_0_r in *. 
  remember (zle 0 (Int.unsigned a - Int.unsigned b)) as d.
  destruct d; inv H; clear Heqd; unfold ch2Z.
    simpl; try rewrite Zplus_0_r.
    assert (R: 0 <= Int.unsigned a - Int.unsigned b < Int.modulus).
          split; trivial.
          specialize (Int.unsigned_range a). 
          specialize (Int.unsigned_range b). intros.
          omega. 
    rewrite Int.unsigned_repr. 
      rewrite Zmod_small; trivial.
    specialize (Z_mod_lt (Int.unsigned a - Int.unsigned b) _ Int.modulus_pos). 
    remember ((Int.unsigned a - Int.unsigned b) mod Int.modulus).
    rewrite <- initialize.max_unsigned_modulus. omega.
  rewrite <- (Z_mod_plus_full (Int.unsigned a - Int.unsigned b) (Int.unsigned Int.one)).
  assert (M: (Int.unsigned Int.one * Int.modulus)%Z = Int.modulus). reflexivity.
  rewrite M in *; clear M.
  remember (Int.unsigned a - Int.unsigned b + Int.modulus) as z.
  assert (BND: 0 <= z < Int.modulus).
          specialize (Int.unsigned_range a). 
          specialize (Int.unsigned_range b). 
          intros. omega.
  clear Heqz. 
  rewrite Zmod_small; trivial.
  rewrite Int.unsigned_repr; trivial.
  rewrite <- initialize.max_unsigned_modulus in BND. omega.
Qed.

Lemma chunk_sub_sound_Carry a b res c:
  chunk_sub a b Int.one = (res,c) ->
    (ch2Z a - ch2Z b - Int.unsigned Int.one) + ch2Z c * Int.modulus = ch2Z res.
Proof. unfold chunk_sub; simpl; intros.
  assert (ONE: 0 <= 1 <= Int.max_unsigned). 
    rewrite initialize.max_unsigned_eq. split; omega. 
  remember (zle 0 (Int.unsigned a - Int.unsigned b- Int.unsigned Int.one)) as d.
  destruct d; inv H; clear Heqd; unfold ch2Z.
    simpl; try rewrite Zplus_0_r.
    assert (R: 0 <= Int.unsigned a - Int.unsigned b - Int.unsigned Int.one < Int.modulus).
          split; trivial.
          specialize (Int.unsigned_range a). 
          specialize (Int.unsigned_range b). intros.
          unfold Int.one in *. simpl in *. rewrite Int.unsigned_repr; trivial. omega. 
      rewrite Zmod_small; trivial.
    rewrite Int.unsigned_repr; trivial.
      rewrite <- initialize.max_unsigned_modulus in R; omega.
  rewrite <- (Z_mod_plus_full (Int.unsigned a - Int.unsigned b- Int.unsigned Int.one) (Int.unsigned Int.one)).
  assert (M: (Int.unsigned Int.one * Int.modulus)%Z = Int.modulus). reflexivity.
  rewrite M in *; clear M.
  remember (Int.unsigned a - Int.unsigned b - Int.unsigned Int.one + Int.modulus) as z.
  assert (BND: 0 <= z < Int.modulus).
          specialize (Int.unsigned_range a). 
          specialize (Int.unsigned_range b). 
          intros. split. unfold Int.one in *; simpl in *.
          rewrite Int.unsigned_repr in *; trivial. omega. omega.
  clear Heqz. 
  rewrite Zmod_small; trivial.
  rewrite Int.unsigned_repr; trivial.
  rewrite <- initialize.max_unsigned_modulus in BND. omega.
Qed.
*)
Lemma chunk_sub_sound a b c res d
  (SUB: chunk_sub a b c = (res,d))
  (HC: c= Int.zero \/ c=Int.one):
  (d= Int.zero \/ d=Int.one) /\
  (ch2Z a - ch2Z b - ch2Z c) + ch2Z d * Int.modulus = ch2Z res.
Proof. unfold chunk_sub in SUB; simpl in *.
  assert (ONE: 0 <= 1 <= Int.max_unsigned). 
    rewrite initialize.max_unsigned_eq. split; omega. 
  remember (zle 0 (Int.unsigned a - Int.unsigned b- Int.unsigned c)) as w.
  destruct w; inv SUB; clear Heqw; unfold ch2Z.
    split. left; trivial.
    simpl; try rewrite Zplus_0_r.
    assert (R: 0 <= Int.unsigned a - Int.unsigned b - Int.unsigned c < Int.modulus).
          split; trivial.
          specialize (Int.unsigned_range a). 
          specialize (Int.unsigned_range b).
          specialize (Int.unsigned_range c). intros. omega.
      rewrite Zmod_small; trivial.
    rewrite Int.unsigned_repr; trivial.
      rewrite <- initialize.max_unsigned_modulus in R; omega.
  split. right; trivial.
  rewrite <- (Z_mod_plus_full (Int.unsigned a - Int.unsigned b- Int.unsigned c) (Int.unsigned Int.one)).
  assert (M: (Int.unsigned Int.one * Int.modulus)%Z = Int.modulus). reflexivity.
  rewrite M in *; clear M.
  remember (Int.unsigned a - Int.unsigned b - Int.unsigned c + Int.modulus) as z.
  assert (BND: 0 <= z < Int.modulus).
          specialize (Int.unsigned_range a). 
          specialize (Int.unsigned_range b). 
          specialize (Int.unsigned_range c). 
          intros. split. 2: omega.
          destruct HC; subst. rewrite Zminus_0_r. omega.
          unfold Int.one in *; simpl in *.
            rewrite Int.unsigned_repr in *; trivial. omega.
  clear Heqz. 
  rewrite Zmod_small; trivial.
  rewrite Int.unsigned_repr; trivial.
  rewrite <- initialize.max_unsigned_modulus in BND. omega.
Qed.

Lemma chunk_sub_sound' a b c res d
  (SUB: chunk_sub a b c = (res,d))
  (HC: c= Int.zero \/ c=Int.one):
  (d= Int.zero \/ d=Int.one) /\
  ch2Z a + ch2Z d * Int.modulus = ch2Z res + ch2Z b + ch2Z c.
Proof. destruct (chunk_sub_sound _ _ _ _ _ SUB); trivial.
  split; trivial. omega.
Qed.

Lemma chunk_sub_gez a b res carry: 
      chunk_sub a b Int.zero = (res, carry) -> 
      0 <= Int.unsigned a - Int.unsigned b -> carry=Int.zero.
Proof. unfold chunk_sub; intros.
  rewrite Zminus_0_r in *.
  destruct (zle 0 (Int.unsigned a - Int.unsigned b)); inv H; trivial.
  omega.
Qed.
  
Lemma chunk_sub_le a b res carry: 
      chunk_sub a b Int.zero = (res, carry) -> 
      Int.unsigned b <= Int.unsigned a -> carry=Int.zero.
Proof. unfold chunk_sub; intros.
  rewrite Zminus_0_r in *.
  destruct (zle 0 (Int.unsigned a - Int.unsigned b)); inv H; trivial.
  omega.
Qed.  

Lemma chunk_sub_gez1 c0 c1 res carry: 
      chunk_sub c0 c1 Int.one = (res, carry) ->
      0 <= Int.unsigned c0 - Int.unsigned c1 - Int.unsigned Int.one ->
      carry=Int.zero.
Proof.
  unfold chunk_sub. intros.
  destruct (zle 0 (Int.unsigned c0 - Int.unsigned c1 - Int.unsigned Int.one)); inv H; trivial.
  omega.
Qed.

Lemma chunk_sub_gtz a b res carry:
   chunk_sub a b Int.zero = (res, carry) ->
   0 > Int.unsigned a - Int.unsigned b -> carry = Int.one.
Proof. unfold chunk_sub. rewrite Zminus_0_r. intros.
  destruct (zle 0 (Int.unsigned a - Int.unsigned b)); inv H; trivial.
  omega.
Qed.

Lemma chunk_sub_lt1 a b res carry: 
      chunk_sub a b Int.one = (res, carry) ->
      0 > Int.unsigned a - Int.unsigned b - Int.unsigned Int.one -> carry = Int.one.
Proof. unfold chunk_sub. intros.
  destruct (zle 0 (Int.unsigned a - Int.unsigned b - Int.unsigned Int.one)); inv H; trivial. 
  omega.
Qed.

Function chunks_sub (ab: list (Chunk * Chunk)) (c:Chunk): (list Chunk) * Chunk :=
  match ab with
    nil => (nil,c)
  | (a1,b1)::t =>
        match chunk_sub a1 b1 c with
          (d, x) => match chunks_sub t x with
                      (res,carry) => (d :: res,carry)
                    end
        end
  end.

Lemma chunks_sub_cons' h t c:
      chunks_sub (h::t) c = 
        match chunk_sub (fst h) (snd h) c with
          (p, d) =>  match chunks_sub t d with
                       (res,e) => (p::res,e)
                     end
        end.
Proof. destruct h. reflexivity. Qed.

Lemma chunks_sub_cons a b t c:
      chunks_sub ((a,b)::t) c = 
        match chunk_sub a b c with
          (p, d) =>  match chunks_sub t d with
                       (res,e) => (p::res,e)
                     end
        end.
Proof.  reflexivity. Qed.

Lemma chunks_sub_sound: forall ab a b (SP: split ab = (a, b)) c res carry
      (HC: c= Int.zero \/ c=Int.one),
      chunks_sub ab c = (res,carry) ->
      chunks2Z (a++[carry]) = chunks2Z res + chunks2Z b + ch2Z c.
Proof.
  induction ab.
    simpl; intros. inv SP; simpl. inv H. simpl. omega.
  intros aS bS SP. simpl in SP. destruct a. remember (split ab) as sp. destruct sp.
    inv SP. rename l into aT. rename l0 into bT.
    specialize (IHab _ _ (eq_refl _)).
    intros. rewrite chunks_sub_cons in H.
    remember (chunk_sub c c0 c1) as X; symmetry in HeqX. destruct X.
    remember (chunks_sub ab c3) as Y; symmetry in HeqY. destruct Y. inv H.
    rewrite <- app_comm_cons.
    do 3 rewrite chunks2Z_cons.
    destruct (chunk_sub_sound' _ _ _ _ _ HeqX); trivial; clear HeqX. 
    rewrite (IHab c3 l); clear IHab; trivial; clear HeqY.
    repeat rewrite Z.mul_add_distr_l. repeat rewrite Z.add_assoc. 
    repeat rewrite <- Z.add_assoc. 
    f_equal. rewrite (Z.add_assoc (ch2Z c2)). rewrite (Z.add_comm (ch2Z c2)).
    rewrite <- Z.add_assoc. f_equal. rewrite Z.add_assoc. rewrite <- H0; clear H0. 
    assert (Int.modulus = 2^32). reflexivity. 
    rewrite H0. rewrite Zmult_comm. apply Z.add_comm.
Qed.