
Definition chunk_mul (a b:Chunk) : list Chunk :=
  let p := (Int.unsigned a * Int.unsigned b)%Z
  in normalize ([Int.repr (p mod Int.modulus); Int.repr(p / Int.modulus)]).

Lemma chunk_mul_sound a b: chunks2Z (chunk_mul a b) = (ch2Z a * ch2Z b)%Z.
Proof.
  unfold chunk_mul. rewrite normalize_sound. repeat rewrite chunks2Z_cons.
  unfold ch2Z. assert (M: 2 ^ 32 = Int.modulus) by reflexivity. rewrite M. clear M.
  remember ((Int.unsigned a * Int.unsigned b)%Z) as u.
  rewrite (Int.unsigned_repr (u mod Int.modulus)).
  Focus 2. specialize (Z_mod_lt u _ Int.modulus_pos). intros.
     destruct H. split; trivial. remember (u mod Int.modulus). 
     rewrite <- initialize.max_unsigned_modulus in H0. omega.
  rewrite Int.unsigned_repr.   
    specialize (Z_div_mod_eq u _ Int.modulus_pos). intros D.
    assert (M: (Int.modulus * chunks2Z []  + u / Int.modulus = 0+u / Int.modulus)%Z).
      f_equal. 
    clear Hequ. remember (Int.modulus * chunks2Z [])%Z.
      rewrite Zplus_0_l in M. rewrite <- M in D. clear M.
    subst z. symmetry. assumption.
  specialize (Int.unsigned_range a). 
    specialize (Int.unsigned_range b). intros; subst.
    split. apply Zdiv_le_lower_bound. omega.
           simpl. apply Z.mul_nonneg_nonneg. apply H0. apply H.
    apply Z.div_le_upper_bound. specialize Int.modulus_pos. omega. 
      rewrite <- initialize.max_unsigned_modulus in H.
      eapply Zmult_le_compat; try omega.
Qed.

(*previous version returns nil in case result is 0 -
the following variant returns at least the least significant
chunk (called v in HAC), and if necessary the u chunk from HAC*) 
Definition chunk_mul' (a b:Chunk) : Chunk * (option Chunk):=
  let p := (Int.unsigned a * Int.unsigned b)%Z
  in if zlt p Int.modulus then (Int.repr p,None)
      else (Int.repr (p mod Int.modulus), Some (Int.repr(p / Int.modulus))).

Lemma chunk_mul'_sound a b p Q (HQ: chunk_mul' a b = (p,Q)):
  match Q with None => ch2Z p 
     | Some q => chunks2Z [p;q]
  end = (ch2Z a * ch2Z b)%Z.
Proof.
  unfold chunk_mul' in HQ.
  destruct (zlt (Int.unsigned a * Int.unsigned b) Int.modulus); inv HQ.
    unfold ch2Z. rewrite Int.unsigned_repr; trivial.
    split; trivial. 
    specialize (Int.unsigned_range a). 
    specialize (Int.unsigned_range b). intros.
    apply Z.mul_nonneg_nonneg. apply H0. apply H.
      rewrite <- initialize.max_unsigned_modulus in l. omega.
  repeat rewrite chunks2Z_cons. unfold ch2Z.
  assert (M: 2 ^ 32 = Int.modulus) by reflexivity. rewrite M. clear M.
  remember ((Int.unsigned a * Int.unsigned b)%Z) as u.
  rewrite (Int.unsigned_repr (u mod Int.modulus)).
  Focus 2. specialize (Z_mod_lt u _ Int.modulus_pos). intros.
     destruct H. split; trivial. remember (u mod Int.modulus). 
     rewrite <- initialize.max_unsigned_modulus in H0. omega.
  rewrite Int.unsigned_repr.   
    specialize (Z_div_mod_eq u _ Int.modulus_pos). intros D.
    assert (M: (Int.modulus * chunks2Z []  + u / Int.modulus = 0+u / Int.modulus)%Z).
      f_equal. 
    clear Hequ. remember (Int.modulus * chunks2Z [])%Z.
      rewrite Zplus_0_l in M. rewrite <- M in D. clear M.
    subst z. symmetry. assumption.
  specialize (Int.unsigned_range a). 
    specialize (Int.unsigned_range b). intros; subst.
    split. apply Zdiv_le_lower_bound. omega.
           simpl. apply Z.mul_nonneg_nonneg. apply H0. apply H.
    apply Z.div_le_upper_bound. specialize Int.modulus_pos. omega. 
      rewrite <- initialize.max_unsigned_modulus in H.
      eapply Zmult_le_compat; try omega.
Qed.

Lemma chunk_mul_mul' a b:
  match chunk_mul' a b with
     (p,None) => normalize [p]
   | (p,Some q) => [p;q]
  end = chunk_mul a b.
Proof. 
  remember (chunk_mul' a b). destruct p. symmetry in Heqp.
  unfold chunk_mul. unfold normalize. simpl.
  unfold chunk_mul' in Heqp.
  remember (Int.unsigned a * Int.unsigned b)%Z as d.
  assert (Hd: 0 <= d).
    specialize (Int.unsigned_range a). 
    specialize (Int.unsigned_range b). intros. subst d. apply Z.mul_nonneg_nonneg; omega.   
  destruct (zlt d Int.modulus).
    clear Heqd. inv Heqp.
    rewrite (Z.div_small d Int.modulus); try split; trivial.
    unfold Int.zero; simpl.
    rewrite Z.mod_small; auto.

  inv Heqp.
  remember (Int.unsigned a * Int.unsigned b)%Z as d.
  remember (Int.eq (Int.repr (d / Int.modulus)) Int.zero) as c. 
  destruct c; simpl; trivial.
  apply binop_lemmas.int_eq_true in Heqc.
  assert (d / Int.modulus < Int.modulus). 
    clear Heqc; subst.
    eapply Zdiv_lt_upper_bound.
      specialize Int.modulus_pos. omega.
      apply Zmult_lt_compat; apply Int.unsigned_range.
   unfold Int.zero. inv Heqc. 
  rewrite Int.Z_mod_modulus_eq in H1.
  remember (Int.unsigned a * Int.unsigned b)%Z as d.
  rewrite Z.mod_small in H1. exfalso.
    specialize (Z_div_mod_eq d _ Int.modulus_pos).
    rewrite H1, Zmult_0_r. simpl. intros. clear - H0 g.
    rewrite H0 in g. clear H0.
    specialize (Z_mod_lt d _ Int.modulus_pos). omega.
  split; trivial.
  apply Z_div_pos; trivial. specialize Int.modulus_pos; omega.
Qed.

Definition chunk_mul'' (a b:Chunk) : Chunk * Chunk:=
  let p := (Int.unsigned a * Int.unsigned b)%Z
  in (Int.repr (p mod Int.modulus), Int.repr(p / Int.modulus)).

Lemma chunk_mul''_sound a b p q (HQ: chunk_mul'' a b = (p,q)):
  chunks2Z [p;q] = (ch2Z a * ch2Z b)%Z.
Proof.
  unfold chunk_mul'' in HQ. inv HQ.
  repeat rewrite chunks2Z_cons. unfold ch2Z.
  assert (M: 2 ^ 32 = Int.modulus) by reflexivity. rewrite M. clear M.
  remember ((Int.unsigned a * Int.unsigned b)%Z) as u.
  rewrite (Int.unsigned_repr (u mod Int.modulus)).
  Focus 2. specialize (Z_mod_lt u _ Int.modulus_pos). intros.
     destruct H. split; trivial. remember (u mod Int.modulus). 
     rewrite <- initialize.max_unsigned_modulus in H0. omega.
  rewrite Int.unsigned_repr.   
    specialize (Z_div_mod_eq u _ Int.modulus_pos). intros D.
    assert (M: (Int.modulus * chunks2Z []  + u / Int.modulus = 0+u / Int.modulus)%Z).
      f_equal. 
    clear Hequ. remember (Int.modulus * chunks2Z [])%Z.
      rewrite Zplus_0_l in M. rewrite <- M in D. clear M.
    subst z. symmetry. assumption.
  specialize (Int.unsigned_range a). 
    specialize (Int.unsigned_range b). intros; subst.
    split. apply Zdiv_le_lower_bound. omega.
           simpl. apply Z.mul_nonneg_nonneg. apply H0. apply H.
    apply Z.div_le_upper_bound. specialize Int.modulus_pos. omega. 
      rewrite <- initialize.max_unsigned_modulus in H.
      eapply Zmult_le_compat; try omega.
Qed.

Definition mul_init n k: list Chunk := list_repeat (n + k +1) Int.zero.

Definition mul_inner_aux (x y: list Chunk) i j (w:list Chunk) (c:Chunk) : list Chunk :=
   let xjyi := chunk_mul (nth j x Int.zero) (nth i y Int.zero) in
   let z := chunks_add' xjyi [c]
   in normalize (chunks_add' z [nth (i+j) w Int.zero]).

Lemma mul_inner_aux_len x y i j w c: (length (mul_inner_aux x y i j w c) <= 2)%nat.
Proof.
  apply length_normalize.
  remember (nth j x Int.zero) as a; clear Heqa.
  remember (nth i y Int.zero) as b; clear Heqb.
  remember (nth (i + j) w Int.zero) as d; clear Heqd. clear.
  do 2 rewrite chunks_add'_sound. rewrite chunk_mul_sound.
  unfold ch2Z.
  assert (Int.modulus ^ Z.of_nat 2 = Int.modulus * Int.modulus)%Z by reflexivity.
  rewrite H; clear H. 
  unfold chunks2Z, ch2Z. rewrite Z.mul_0_r. repeat rewrite Z.add_0_l.
  specialize (Int.unsigned_range a). 
  specialize (Int.unsigned_range b). 
  specialize (Int.unsigned_range c). 
  specialize (Int.unsigned_range d).
  specialize (Int.modulus_pos); intros. 
  rewrite <- initialize.max_unsigned_modulus in *. (* destruct H0; destruct H1; destruct H2; destruct H3.*)
  assert (Int.unsigned a * Int.unsigned b <= Int.max_unsigned * Int.max_unsigned).
    apply Zmult_le_compat; omega.
  eapply Z.le_lt_trans.
  instantiate (1:= Int.max_unsigned * Int.max_unsigned + Int.unsigned c + Int.unsigned d). omega.
  clear H4. 
  rewrite Z.mul_add_distr_r. rewrite Z.mul_1_l. 
  rewrite Z.mul_add_distr_l. rewrite Z.mul_1_r. omega.
Qed. 

Lemma chunk_mul_sound a b: chunks2Z (chunk_mul a b) = (ch2Z a * ch2Z b)%Z.
Proof.
  unfold chunk_mul. rewrite normalize_sound. repeat rewrite chunks2Z_cons.
  unfold ch2Z. assert (M: 2 ^ 32 = Int.modulus) by reflexivity. rewrite M. clear M.
  remember ((Int.unsigned a * Int.unsigned b)%Z) as u.
  rewrite (Int.unsigned_repr (u mod Int.modulus)).
  Focus 2. specialize (Z_mod_lt u _ Int.modulus_pos). intros.
     destruct H. split; trivial. remember (u mod Int.modulus). 
     rewrite <- initialize.max_unsigned_modulus in H0. omega.
  rewrite Int.unsigned_repr.   
    specialize (Z_div_mod_eq u _ Int.modulus_pos). intros D.
    assert (M: (Int.modulus * chunks2Z []  + u / Int.modulus = 0+u / Int.modulus)%Z).
      f_equal. 
    clear Hequ. remember (Int.modulus * chunks2Z [])%Z.
      rewrite Zplus_0_l in M. rewrite <- M in D. clear M.
    subst z. symmetry. assumption.
  specialize (Int.unsigned_range a). 
    specialize (Int.unsigned_range b). intros; subst.
    split. apply Zdiv_le_lower_bound. omega.
           simpl. apply Z.mul_nonneg_nonneg. apply H0. apply H.
    apply Z.div_le_upper_bound. specialize Int.modulus_pos. omega. 
      rewrite <- initialize.max_unsigned_modulus in H.
      eapply Zmult_le_compat; try omega.
Qed.