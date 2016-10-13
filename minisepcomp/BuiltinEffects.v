
Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Events.
Require Import Memory.
Require Import Globalenvs.
Require Import sepcomp.mem_lemmas.
Require Import sepcomp.effect_semantics.

Definition o_o_reach (j:meminj) L2 m1 b2 ofs := 
  L2 b2 = true /\ 
 (forall b1 delta (J:j b1 = Some(b2,delta)),
          ~ Mem.perm m1 b1 (ofs-delta) Max Nonempty). 

Parameter EFisHelper: external_function -> Prop. 
Parameter observableEF: external_function -> Prop. 
Axiom observableEF_dec: forall ef, {observableEF ef} + {~observableEF ef}.
Axiom EFhelpers: forall ef, EFisHelper ef -> ~observableEF (*hf*) ef.
(*LENB: TODO: replace these parameters and axioms by importing/adapting the correct CompComp2.1 file,
  add Variable hf : I64Helpers.helper_functions. and adapt treatment of
  obervables, builtins etc*)

Parameter nonobservables_mem_extends: forall {F V TF TV:Type}
       (ge:Genv.t F V) (tge:Genv.t TF TV) ef vargs m t v m'
          (EC: external_call ef ge vargs m t v m') (NOBS: ~observableEF ef) tm tvargs, 
    Mem.extends m tm ->
    Val.lessdef_list vargs tvargs ->
    exists tv, exists tm',
       external_call ef tge tvargs tm t tv tm'
    /\ Val.lessdef v tv
    /\ Mem.extends m' tm'
    /\ Mem.unchanged_on (loc_out_of_bounds m) tm tm'.

(*plays role of external_call_mem_inject.*)
Parameter nonobservables_mem_inject: forall {F V TF TV:Type}
       (ge:Genv.t F V) (tge:Genv.t TF TV) (*(GDE: genvs_domain_eq ge tge) *)
       (*(SymbPres: symbols_preserved)*)
       j (SymbsInj: symbols_inject j ge tge)
       (*hf*) ef vargs m t vres m1 tm vargs'
       (*(SMV: sm_valid mu m tm) (RC: REACH_closed m (vis mu))
       (Glob: forall b, isGlobalBlock ge b = true -> 
              frgnBlocksSrc mu b = true)*)
       (OBS: ~ observableEF (*hf*) ef)
       L TL
       (HLTL : forall b b' d, j b = Some (b', d) -> L b = TL b')
       (HL : forall b, L b = true -> Mem.valid_block m b)
       (HTL : forall b, TL b = true -> Mem.valid_block tm b),
       meminj_preserves_globals ge j ->
       external_call ef ge vargs m t vres m1 ->
       Mem.inject j m tm ->
       Val.inject_list j vargs vargs' ->
       exists j' vres' tm1,
         external_call ef tge vargs' tm t vres' tm1 /\
         Val.inject j' vres vres' /\
         Mem.inject j' m1 tm1 /\
         Mem.unchanged_on (fun b1 ofs => L b1 = true /\ j b1 = None) m m1 /\
         Mem.unchanged_on (o_o_reach j TL m) tm tm1 /\
         inject_incr j j' /\
         inject_separated j j' m tm .


(*
Parameter nonobservables_no_alloc: forall {F V} ef (ge : Genv.t F V) args m t v m' 
          (EC: external_call ef ge args m t v m') (NOBS: ~observableEF ef), 
          freshblock m m' = fun b => false.
*)

Definition memcpy_Effect sz vargs m:=
       match vargs with 
          Vptr b1 ofs1 :: Vptr b2 ofs2 :: nil =>
          fun b z => eq_block b b1 && zle 0 sz && zle (Int.unsigned ofs1) z &&
                     zlt z (Int.unsigned ofs1 + sz) && valid_block_dec m b
       | _ => fun b z => false
       end.
      
Definition free_Effect vargs m:=
       match vargs with 
          Vptr b1 lo :: nil =>
          match Mem.load Mint32 m b1 (Int.unsigned lo - 4)
          with Some (Vint sz) =>
            fun b z => eq_block b b1 &&  zlt 0 (Int.unsigned sz) &&
                     zle (Int.unsigned lo - 4) z &&
                     zlt z (Int.unsigned lo + Int.unsigned sz)
          | _ => fun b z => false
          end
       | _ => fun b z => false
       end.

Definition BuiltinEffect  {F V: Type} (ge: Genv.t F V) (ef: external_function)
          (vargs:list val) (m:mem): block -> Z -> bool :=
  match ef with
    EF_malloc => EmptyEffect
  | EF_free => free_Effect vargs m
  | EF_memcpy sz a => memcpy_Effect sz vargs m
  | _ => fun b z => false
  end.

(*proof in CompComp2.1's BuiltinEffects.v*)
Axiom BuiltinEffect_unchOn:
    forall {F V:Type} (*hf*) ef (g : Genv.t F V) vargs m t vres m'
    (OBS: ~ observableEF (*hf*) ef),
    external_call ef g vargs m t vres m' -> 
    Mem.unchanged_on
      (fun b z=> BuiltinEffect g ef vargs m b z = false) m m'.

Lemma BuiltinEffect_CurWR {F V: Type} (ge: Genv.t F V) ef args m res t m'
      (EXT: external_call ef ge args m t res m') b z
      (HE : BuiltinEffect ge ef args m b z = true):
Mem.perm m b z Cur Writable.
Proof. unfold BuiltinEffect in HE. destruct ef; try discriminate.
  - unfold free_Effect in HE. destruct args; try discriminate. destruct v; try discriminate.
    destruct args; try discriminate.
    remember (Mem.load Mint32 m b0 (Int.unsigned i - 4)) as q; destruct q; try discriminate.
    destruct v; try discriminate. 
    destruct (eq_block b b0); simpl in HE; try discriminate. subst b0.
    destruct (zlt 0 (Int.unsigned i0)); simpl in HE; try discriminate.
    destruct (zle (Int.unsigned i - 4) z); simpl in HE; try discriminate.
    destruct (zlt z (Int.unsigned i + Int.unsigned i0)); simpl in HE; try discriminate.
    simpl in EXT; inv EXT. rewrite H1 in Heqq. inv Heqq.
    eapply Mem.perm_implies. eapply Mem.free_range_perm. eassumption. omega. constructor.
  - unfold memcpy_Effect in HE. destruct args; try discriminate. destruct v; try discriminate.
    destruct args; try discriminate. destruct v; try discriminate.
    destruct args; try discriminate. destruct (eq_block b b0); simpl in HE; try discriminate. subst b0.
    destruct (zle 0 sz); try discriminate; simpl in *.
    destruct (zle (Int.unsigned i) z); simpl in HE; try discriminate.
    destruct (zlt z (Int.unsigned i + sz)); simpl in HE; try discriminate.
    simpl in EXT; inv EXT.
    apply Mem.loadbytes_length in H13.
    eapply Mem.storebytes_range_perm. eassumption. rewrite H13, nat_of_Z_eq; trivial. omega.
Qed.

Lemma BuiltinEffects_propagate_extends:
 forall {F V TF TV:Type}
       (ge:Genv.t F V) (tge:Genv.t TF TV) ef args m t res m' args' m2 res' m2' b ofs
   (EC_SRC: external_call ef ge args m t res m')
   (ARGS: Val.lessdef_list args args')
   (PreExt: Mem.extends m m2)
   (*(OBS: ~ observableEF ef)*)
   (EC_TGT : external_call ef tge args' m2 t res' m2')
   (*(RES: Val.lessdef res res')
   (PostExt: Mem.extends m' m2')*)
   (Eff: BuiltinEffect tge ef args' m2 b ofs = true),
 BuiltinEffect ge ef args m b ofs = true.
Proof. intros.
 intros. destruct ef; simpl in *; try discriminate.
+ (*free*)
  inv EC_SRC. inv EC_TGT. simpl in *.
  rewrite H. rewrite H2 in Eff.
  inv ARGS. inv H8. clear H10. 
  exploit Mem.load_extends. apply PreExt. eassumption. intros [v2 [LD LDv]].
  rewrite LD in H2. inv H2. inv LDv. trivial.
+ (*memcpy*)
  inv EC_SRC. inv EC_TGT. simpl in *.
  inv ARGS. inv H18. inv H20. inv H18.
  destruct (eq_block b bdst0); simpl in *; try discriminate. subst bdst0.
  destruct (zle 0 sz); try discriminate; simpl in *.   
  destruct (zle (Int.unsigned odst0) ofs); simpl in *; try discriminate.
  destruct (zlt ofs (Int.unsigned odst0 + sz)); simpl in *; try discriminate.
  destruct (valid_block_dec m2 b); try discriminate.
  destruct (valid_block_dec m b); trivial; simpl.
  elim n. eapply Mem.valid_block_extends; eauto.
Qed. 

Lemma BuiltinEffects_propagate_injects:
 forall {F V TF TV:Type}
       (ge:Genv.t F V) (tge:Genv.t TF TV) ef args m t res j j' m' args' m2 res' m2' bb ofs
   (EC_SRC: external_call ef ge args m t res m')
   (ARGS: Val.inject_list j args args')
   (MINJ: Mem.inject j m m2)
   (*(OBS: ~ observableEF ef)*)
   (EC_TGT : external_call ef tge args' m2 t res' m2')
   (INC: inject_incr j j') (*
   (RES: Val.inject j' res res')
   (PostExt: Mem.inject j' m' m2')*)
   (Eff: BuiltinEffect tge ef args' m2 bb ofs = true),
   exists (b1 : block) (delta : Z),
      j b1 = Some (bb, delta) /\
      BuiltinEffect ge ef args m b1 (ofs - delta) = true.
Proof. intros.
 intros. destruct ef; simpl in *; try discriminate.
+ (*free*)
  inv EC_SRC. inv EC_TGT. simpl in *.
  rewrite H. rewrite H2 in Eff.
  inv ARGS. inv H8. clear H10. 
  exploit Mem.load_inject. eassumption. eassumption. eassumption. intros [v2 [TLD LDv]].
  assert (RP: Mem.range_perm m b (Int.unsigned lo - 4)
                               (Int.unsigned lo + Int.unsigned sz) Cur Freeable).
    { eapply Mem.free_range_perm; eauto.  }
  exploit Mem.address_inject. eapply MINJ. 
    { apply Mem.perm_implies with Freeable; auto with mem.
      apply RP. instantiate (1 := lo). omega. }
  eassumption. 
  intro EQ.
  rewrite EQ in *.
  assert (Arith4: Int.unsigned lo - 4 + delta = Int.unsigned lo + delta - 4) by omega.
  rewrite Arith4, TLD in *.
  destruct (eq_block bb b0); subst; simpl in *; try discriminate.
  inv H2. inv LDv. eexists; eexists; split. eassumption.
  destruct (eq_block b b); simpl. 2: elim n; trivial. clear e.
  destruct (zlt 0 (Int.unsigned sz0)); trivial; simpl in *; try discriminate.
  destruct (zle (Int.unsigned lo + delta - 4) ofs); trivial; simpl in *; try discriminate.
  destruct (zlt ofs (Int.unsigned lo + delta + Int.unsigned sz0)); trivial; simpl in *; try discriminate.
  destruct (zle (Int.unsigned lo - 4) (ofs - delta)); simpl; try omega.   
  destruct (zlt (ofs - delta) (Int.unsigned lo + Int.unsigned sz0)); simpl; trivial; try omega.
+ (*memcpy*)
  inv EC_SRC. inv EC_TGT. simpl in *.
  exploit Mem.loadbytes_length. apply H5. intros LBytes.
  exploit Mem.loadbytes_length. apply H13. intros LBytes'. clear H2 H3 H10 H11 H7 H H1 H9 H8.
  inv ARGS. inv H3. inv H8. inv H3. clear H10.
  destruct (eq_block bb bdst0); simpl in *; try discriminate. subst bdst0.
  exists bdst, delta; split; trivial.
  destruct (eq_block bdst bdst); simpl. 2: elim n; trivial. clear e.
  destruct (zle 0 sz); try discriminate; simpl in *.   
  destruct (zle (Int.unsigned (Int.add odst (Int.repr delta))) ofs); simpl in *; try inv Eff. 
  destruct (zlt ofs (Int.unsigned (Int.add odst (Int.repr delta)) + sz)); simpl in *; try inv H1.
  exploit Mem.address_inject. eapply MINJ. 2: apply H7.
      eapply Mem.storebytes_range_perm. eassumption.
      exploit Mem.loadbytes_length. apply H5. intros X; rewrite X, nat_of_Z_eq.
      instantiate (1:=odst). omega. omega.
  intros A; rewrite A in l0.
    destruct (zle (Int.unsigned odst) (ofs - delta)); simpl. 2: omega.
    destruct (zlt (ofs - delta) (Int.unsigned odst + sz)); simpl. 2: omega.
    destruct (valid_block_dec m bdst); destruct (valid_block_dec m2 bb); simpl; trivial.
    elim n. eapply Mem.valid_block_inject_2; eassumption.  
    elim n. eapply Mem.valid_block_inject_1; eassumption.
Qed.

Lemma senv_equiv_trans {F1 V1 F2 V2 F3 V3} (g1 : Genv.t F1 V1)
  (g2 : Genv.t F2 V2) (g3 : Genv.t F3 V3):
  Senv.equiv g1 g2 -> Senv.equiv g2 g3 -> Senv.equiv g1 g3.
Proof. intros [A1 [A2 A3]] [B1 [B2 B3]]. 
repeat split; intros.
rewrite B1; apply A1.
rewrite B2; apply A2.
rewrite B3; apply A3.
Qed.

Lemma symbols_inject_trans {F1 V1 F2 V2 F3 V3} (g1 : Genv.t F1 V1)
  (g2 : Genv.t F2 V2) (g3 : Genv.t F3 V3) (j k: meminj):
  symbols_inject j g1 g2 -> symbols_inject k g2 g3 ->
  symbols_inject (compose_meminj j k) g1 g3.
Proof. intros [A1 [A2 [A3 A4]]] [B1 [B2 [B3 B4]]].
split. intros. rewrite B1; apply A1. 
split. intros. apply compose_meminjD_Some  in H. destruct H as [? [? [? [? [? ?]]]]].
   destruct (A2 _ _ _ _ H H0). subst x0 delta; simpl.
   eapply B2; eauto. 
split; intros. destruct (A3 _ _ H H0) as [? [? ?]]. rewrite <- A1 in H.
  destruct (B3 _ _ H H2) as [? [? ?]].
  exists x0; split; trivial. unfold compose_meminj. rewrite H1, H3; trivial.
apply compose_meminjD_Some  in H. destruct H as [? [? [? [? [? ?]]]]]. subst.
  rewrite (B4 _ _ _ H0). apply (A4 _ _ _ H).
Qed. 

Lemma IGB: forall {F V} (g:Genv.t F V) b, 
  isGlobalBlock g b = true -> Plt b (Genv.genv_next g).
Proof. unfold isGlobalBlock, genv2blocksBool. simpl. intros.
remember (Genv.invert_symbol g b) as q.
destruct q; symmetry in Heqq; simpl in *.
+ apply Genv.invert_find_symbol in Heqq.
  eapply Genv.genv_symb_range. apply Heqq. 
+ remember (Genv.find_var_info g b) as w.
  destruct w; symmetry in Heqw; try discriminate.
  unfold Genv.find_var_info, Genv.find_def in Heqw.
     remember ((Genv.genv_defs g) ! b ) as t. destruct t; inv Heqw. destruct g1; inv H1. 
     eapply Genv.genv_defs_range. rewrite <- Heqt; reflexivity.
Qed.

