Require Import Coqlib.
Require Import Integers.
Require Import compcert.common.Values.
Require Import Maps.
Require Import Events. (*needed for some definitions (loc_out_of_reach etc*)
Require Import Memory.
Require Import VST.msl.Axioms.

Require Import VST.coarse_sepcomp.coarse_defs.
Require Import VST.coarse_sepcomp.coarse_base.
Require Import VST.coarse_sepcomp.FiniteMaps. 

Section EI_construction.
Variable (j23:meminj) (m1 m1' m2 : mem) (L2 B:block -> bool).
Definition ACCESS:= fun b2 ofs2 k =>
       if valid_block_dec m2 b2 then 
         if B b2 then PMap.get b2 m2.(Mem.mem_access) ofs2 k else
           if L2 b2 then
               if Mem.perm_dec m1 b2 ofs2 Max Nonempty  
               then PMap.get b2 m1'.(Mem.mem_access) ofs2 k
               else PMap.get b2 m2.(Mem.mem_access) ofs2 k
           else if Mem.perm_dec m1 b2 ofs2 Max Nonempty 
                then PMap.get b2 m1'.(Mem.mem_access) ofs2 k
                else None 
       else PMap.get b2 m1'.(Mem.mem_access) ofs2 k.

Lemma mkAccessMap_EI_existsT (VB : (Mem.nextblock m2 <= Mem.nextblock m1')%positive):
      { M : PMap.t (Z -> perm_kind -> option permission) |
          fst M = (fun k ofs => None) /\
          forall b, PMap.get b M = ACCESS b}.
Proof. 
  apply (pmap_construct_c _ ACCESS (Mem.nextblock m1') (fun ofs k => None)).
  intros; unfold ACCESS; extensionality ofs; extensionality k.
  destruct (valid_block_dec m2 n); [ unfold Mem.valid_block in v; xomega|].
  remember ((Mem.mem_access m1') !! n ofs k) as p; symmetry in Heqp.
  specialize (Mem.perm_valid_block m1' n ofs k); unfold Mem.perm. rewrite Heqp; intros.
  destruct p; trivial.
  specialize (H0 p (perm_refl _)). unfold Mem.valid_block in H0; xomega.
Qed.

Definition CONT := fun b2 ofs2 =>
  if valid_block_dec m2 b2 then 
    if B b2 then ZMap.get ofs2 (m2.(Mem.mem_contents) !! b2) else
    if L2 b2 then match j23 b2 with 
                 None => ZMap.get ofs2 (m2.(Mem.mem_contents) !! b2)
               | Some _ => if Mem.perm_dec m1 b2 ofs2 Max Nonempty 
                           then ZMap.get ofs2 (PMap.get b2 m1'.(Mem.mem_contents))
                           else ZMap.get ofs2 ( m2.(Mem.mem_contents) !! b2)
                  end
      else if Mem.perm_dec m1 b2 ofs2 Max Nonempty 
        then ZMap.get ofs2 (PMap.get b2 m1'.(Mem.mem_contents))
        else match j23 b2 with 
               None =>  ZMap.get ofs2 ( m2.(Mem.mem_contents) !! b2)
             | Some (b3,d3) =>  Undef 
             end
  else if Mem.perm_dec m1' b2 ofs2 Max Nonempty
      then ZMap.get ofs2 (PMap.get b2 m1'.(Mem.mem_contents))
      else Undef. (*ZMap.get ofs2 (fst (Mem.mem_contents m2)).*)

Lemma CM_block_EI_existsT: forall b,
  { M : ZMap.t memval | fst M = Undef /\ forall ofs, ZMap.get ofs M = CONT b ofs}.
Proof. intros.
  remember (zmap_finite_c _ (PMap.get b m1'.(Mem.mem_contents))) as LH1.
  apply eq_sym in HeqLH1. destruct LH1 as [lo1 hi1].
  specialize (zmap_finite_sound_c _ _ _ _ HeqLH1).
  intros Bounds1; clear HeqLH1.
  remember (zmap_finite_c _ (PMap.get b m2.(Mem.mem_contents))) as LH2.
  apply eq_sym in HeqLH2. destruct LH2 as [lo2 hi2].
  specialize (zmap_finite_sound_c _ _ _ _ HeqLH2).
  intros Bounds2; clear HeqLH2.
   assert (Undef2: fst (Mem.mem_contents m2) !! b = Undef). apply m2.
   assert (Undef1: fst (Mem.mem_contents m1') !! b = Undef). apply m1'.
   rewrite Undef2 in *. rewrite Undef1 in *. (*clear Undef1 Undef2.*)

  destruct (zmap_construct_c _ (CONT b) (Z.min lo1 lo2) (Z.max hi1 hi2) Undef) as [M PM].
  { intros n N; unfold CONT; rewrite (Bounds1 n), (Bounds2 n).
    + destruct (valid_block_dec m2 b); simpl.
      - destruct (B b); trivial.
        destruct (Mem.perm_dec m1 b n Max Nonempty); destruct (j23 b); destruct (L2 b); trivial.
        destruct p; trivial.
      - destruct (Mem.perm_dec m1' b n Max Nonempty); trivial. 
    + destruct N as [N | N].
      - apply Z.min_glb_lt_iff in N. omega.
      - destruct (Z.max_lub_lt_iff hi1 hi2 n) as [M _]; destruct M ; omega.
    + destruct N as [N | N].
      - apply Z.min_glb_lt_iff in N. omega.
      - destruct (Z.max_lub_lt_iff hi1 hi2 n) as [M _]; destruct M ; omega. }
  exists M. apply PM.
Qed.

Definition ContentsMap_EI_FUN (b:block): ZMap.t memval.
destruct (plt b (Mem.nextblock m1')).
  apply(CM_block_EI_existsT b). apply (ZMap.init Undef).
Defined.

Lemma ContentsMap_EI_existsT:
      { M : PMap.t (ZMap.t memval) |
        fst M = ZMap.init Undef /\ forall b, PMap.get b M = ContentsMap_EI_FUN b}.
Proof.
  apply (pmap_construct_c _ ContentsMap_EI_FUN (Mem.nextblock m1') (ZMap.init Undef)).
  intros. unfold ContentsMap_EI_FUN.
  remember (plt n (Mem.nextblock m1')) as d.
  destruct d; [ exfalso; xomega | trivial].
Qed.

Lemma interpolation_EI_exists
    (NB21': (Mem.nextblock m2 <= Mem.nextblock m1')%positive):
    exists m2', (forall b ofs, ZMap.get ofs (Mem.mem_contents m2') !! b = 
                               CONT b ofs) /\
                (forall b, (Mem.mem_access m2') !! b = ACCESS b) /\  
                (Mem.nextblock m2' = Mem.nextblock m1').
Proof.
  (*Access*)
  destruct mkAccessMap_EI_existsT as [access [ACC1 ACC2]]; trivial.
   
  (*Content*)
  destruct ContentsMap_EI_existsT as [contents [CONT1 CONT2]].

  assert (P1: forall b ofs, Mem.perm_order'' (access !! b ofs Max) (access !! b ofs Cur)).
  { intros. rewrite ACC2; unfold ACCESS; clear.
    destruct (valid_block_dec m2 b); [| apply m1'].
    destruct (B b); [apply m2 | ].
    destruct (L2 b). destruct (Mem.perm_dec m1 b ofs Max Nonempty); [apply m1' | apply m2].
    destruct (Mem.perm_dec m1 b ofs Max Nonempty); [apply m1' | simpl; trivial]. }

  assert (P2: forall b ofs k, ~ Plt b (Mem.nextblock m1') -> access !! b ofs k = None).
  { intros. rewrite ACC2; unfold ACCESS; clear - NB21' H.
    destruct (valid_block_dec m2 b). unfold Mem.valid_block in v. xomega.
    apply m1'; trivial. }  

  assert (P3: forall b, fst contents !! b = Undef).
  { intros. rewrite CONT2. unfold ContentsMap_EI_FUN. 
    destruct (CM_block_EI_existsT b) as [X [Y A]].
    destruct (plt b (Mem.nextblock m1')); trivial. } 

  exists (Mem.mkmem contents access (Mem.nextblock m1') P1 P2 P3); simpl;
  split; [ simpl; intros | split; [apply ACC2 | trivial]]. 
  rewrite CONT2; clear CONT2; unfold ContentsMap_EI_FUN.
  destruct (CM_block_EI_existsT b) as [C [X Y]].
    destruct (plt b (Mem.nextblock m1')); [ apply Y |]. 
    unfold CONT; destruct (valid_block_dec m2 b). 
    - elim n; clear -v NB21'. unfold Mem.valid_block in v; xomega.
    - destruct (Mem.perm_dec m1' b ofs Max Nonempty); [| apply ZMap.gi].
      apply Mem.perm_valid_block in p. unfold Mem.valid_block in p; xomega.
Qed.
End EI_construction.

Section Interpolation_EI.
  Variable m1 m2 m1' m3 m3':mem.
  Variable j j': meminj.
  Variable LS LT B1 B2 B3: block -> bool.
  (*Variable LSvalid : forall b, LS b = true -> Mem.valid_block m2 b.
    Variable LTvalid : forall b, LT b = true -> Mem.valid_block m3 b. not needed*)
  Variable JValid : forall  b1 b2 d,  j b1 = Some (b2, d) -> Mem.valid_block m2 b1 /\ Mem.valid_block m3 b2.
  Variable Ext12: Mem.extends m1 m2.
  Variable Fwd1: mem_forward m1 m1'.
  Variable Inj23: Mem.inject j m2 m3.
  (*Variable Fwd3: mem_forward m3 m3'. not needed!*)
  Variable Inj13': Mem.inject j' m1' m3'.
  Variable UnchSrc : Mem.unchanged_on (fun b1 _ => LS b1 = true /\ j b1 = None) m1 m1'.
  Variable UnchTgt : Mem.unchanged_on (fun b z => LT b = true /\ loc_out_of_reach j m1 b z) m3 m3'.
  Variable INC : inject_incr j j'. 
  Variable ESEP: esep m2 j j' m3 LT.
  Variable local: forall b1 b2 d, j b1 = Some(b2,d) -> LS b1 = LT b2.
  Variable B2valid : forall b, B2 b = true -> Mem.valid_block m2 b /\ forall ofs, ~ Mem.perm m2 b ofs Max Writable.
  Variable Gsep: forall b2 b3 d, j b2 = None -> j' b2 = Some(b3,d) -> B3 b3 = false.
  Variable B2_B3: forall b2 b3 d, j b2 = Some (b3, d) -> B2 b2 = true -> B3 b3 = true.
  Variable B2_B1: forall b, B2 b = true -> B1 b = true.
  Variable B2_LS: forall b, B2 b = true -> LS b = false.
  Variable RDOnly_fwd1: RDOnly_fwd m1 m1' B1.
  Variable RDOnly_fwd3: RDOnly_fwd m3 m3' B3.

Lemma NB: Mem.nextblock m1 = Mem.nextblock m2. apply Ext12. Qed.

Lemma VB b: Mem.valid_block m1 b = Mem.valid_block m2 b.
Proof. unfold Mem.valid_block. rewrite NB; trivial. Qed.

Lemma interp_EI: exists m2',
  Mem.extends m1' m2' /\
  mem_forward m2 m2' /\
  Mem.inject j' m2' m3' /\
  RDOnly_fwd m2 m2' B2 /\
(*  Mem.unchanged_on (o_o_reach (Mem.flat_inj (Mem.nextblock m1)) L1 m1) m2 m2' /\*)
  Mem.unchanged_on (fun b z => LS b = true /\ loc_out_of_bounds m1 b z) m2 m2' /\
  Mem.unchanged_on (fun b _ => LS b = true /\ j b = None) m2 m2'.
Proof. 
destruct (interpolation_EI_exists j m1 m1' m2 LS B2) as [m2' [H_CONT [H_ACCESS NB']]].
{ rewrite <- NB. apply mem_forward_nextblock; trivial. }

exists m2'.
assert (VB' : forall b : block, Mem.valid_block m1' b = Mem.valid_block m2' b).
{ intros; unfold Mem.valid_block. rewrite NB'; trivial. }

assert (Inj13:= Mem.extends_inject_compose _ _ _ _ Ext12 Inj23).
assert (MMU_LU: Mem.unchanged_on (fun b _ => LS b = true /\ j b = None) m2 m2' ).
{ split. 
  + rewrite NB', <- (Mem.mext_next _ _ Ext12). eapply mem_forward_nextblock. trivial. 
  + intros. destruct H as [Lb Jb].
    unfold Mem.perm at 2. rewrite H_ACCESS. unfold ACCESS. clear H_CONT H_ACCESS.
    destruct (valid_block_dec m2 b); try contradiction. rewrite Lb.
    remember (B2 b) as q; destruct q. split; auto.
    remember (Mem.perm_dec m1 b ofs Max Nonempty) as w.
    destruct w. 2: split; eauto.
    split; intros. 
    - apply UnchSrc. split; trivial. rewrite Mem.valid_block_extends; eassumption.
      destruct (Mem.mext_perm_inv _ _ Ext12 _ _ _ _ H). trivial. contradiction.
    - apply UnchSrc in H. 2: split; trivial. 2: rewrite Mem.valid_block_extends; eassumption.
      eapply Mem.perm_extends; eassumption.
  + intros. destruct H as [Lb Jb]. rewrite H_CONT; clear H_CONT. unfold  CONT.
    specialize (Mem.perm_valid_block _ _ _ _ _ H0); intros vb2.
    destruct (valid_block_dec m2 b); try contradiction. rewrite <- VB in v.
    rewrite Jb, Lb.
    remember (B2 b) as q; symmetry in Heqq.
    destruct q; [ apply B2_LS in Heqq; congruence | trivial]. }
assert (Fwd2: mem_forward m2 m2').
{ split; intros. 
  + (*valid_block*) apply (Mem.valid_block_extends _ _ b Ext12) in B. 
        apply Fwd1 in B. destruct B as[H _]. rewrite <- VB'. apply H. 
  + (*max*)
    unfold Mem.perm in H. rewrite H_ACCESS in H; clear H_ACCESS H_CONT. unfold ACCESS in H.
    destruct (valid_block_dec m2 b); try contradiction.
    remember (B2 b) as q; symmetry in Heqq.
    destruct q; trivial.
    remember (LS b) as w; symmetry in Heqw.
    destruct w.
    { remember (Mem.perm_dec m1 b ofs Max Nonempty) as t.
      destruct t;  trivial. clear Heqt.
      eapply Mem.perm_extends. eassumption.
      apply Fwd1; trivial. rewrite VB; trivial. }
    remember (Mem.perm_dec m1 b ofs Max Nonempty) as t.
    destruct t; [clear Heqt | contradiction].
    eapply Mem.perm_extends. eassumption.
    apply Fwd1; trivial. rewrite VB; trivial. } 
assert (RDOnly_fwd2: RDOnly_fwd m2 m2' B2). (*same proof as in interp_II, but for different H_ACCESS, H_CONT*)
{ clear - B2valid H_ACCESS H_CONT. red; intros b Hb. destruct (B2valid _ Hb) as [VB2 RDOb2]. red; intros. 
  assert (P: forall i, 0 <= i < n -> forall k p, Mem.perm m2 b (ofs + i) k p <-> Mem.perm m2' b (ofs + i) k p).
  { intros. unfold Mem.perm; rewrite H_ACCESS. unfold ACCESS; simpl.
    destruct (valid_block_dec m2 b); [ rewrite Hb; split; trivial | contradiction]. }
  split; trivial. 
  remember (Mem.loadbytes m2' b ofs n) as q; remember (Mem.loadbytes m2 b ofs n) as p.
  symmetry in Heqq; symmetry in Heqp; destruct p; destruct q; trivial;
    try apply loadbytes_D in Heqp; try apply loadbytes_D in Heqq.
  - destruct Heqq; destruct Heqp; subst; f_equal; apply Mem.getN_exten; intros.
      rewrite (H_CONT b); clear H_CONT. unfold CONT; simpl.
      destruct (valid_block_dec m2 b); [ rewrite Hb; trivial | contradiction].
    - destruct Heqp; subst.
      destruct (Mem.range_perm_dec m2' b ofs (ofs + n) Cur Readable). 
      * apply Mem.range_perm_loadbytes in r. destruct r as [bytes R]; congruence.
      * elim n0; clear n0. red; intros. specialize (P (ofs0 - ofs)).
        rewrite Zplus_minus in P; apply P; [ omega | apply (H _ H0)].
    - destruct Heqq; subst.
      destruct (Mem.range_perm_dec m2 b ofs (ofs + n) Cur Readable). 
      * apply Mem.range_perm_loadbytes in r. destruct r as [bytes R]; congruence.
      * elim n0; clear n0. red; intros. specialize (P (ofs0 - ofs)).
        rewrite Zplus_minus in P; apply P; [ omega | apply (H _ H0)]. }
(*assert (MMU_LOOR: Mem.unchanged_on (o_o_reach (Mem.flat_inj (Mem.nextblock m1)) L1 m1) m2 m2'). 
{ split.
  + apply MMU_LU.
  + intros. destruct H as [Lb Pb].
    unfold Mem.perm at 2. rewrite H_ACCESS; clear H_ACCESS H_CONT. unfold ACCESS.
    destruct (valid_block_dec m2 b); try contradiction.
    rewrite Lb. rewrite <- VB in H0. specialize (Pb b 0). rewrite Zminus_0_r, flatinj_I in Pb; trivial.
    remember (B2 b) as q; symmetry in Heqq.
    destruct q. { split; auto. }
    remember (Mem.perm_dec m1 b ofs Max Nonempty) as t.
    destruct t. 
    { elim Pb; trivial. }
    { split; auto. }
  + intros. destruct H as [Lb Pb]. rewrite H_CONT; clear H_CONT. unfold CONT.
    destruct (valid_block_dec m2 b). 2: solve [elim n; eapply Mem.perm_valid_block; eassumption].
    rewrite Lb.
    destruct (B2 b); trivial.
    remember (Mem.perm_dec m1 b ofs Max Nonempty) as w.
    destruct w; trivial.
    rewrite <- VB in v.
    specialize (Pb b 0). rewrite flatinj_I, Zminus_0_r in Pb; trivial.
    elim Pb; trivial.
    destruct (j b); trivial. }*)
assert (MMU_LOOR : Mem.unchanged_on (fun (b : block) (z : Z) => LS b = true /\ loc_out_of_bounds m1 b z) m2 m2').
{ split.
  + apply MMU_LU.
  + intros. destruct H as [Lb Pb].
    unfold Mem.perm at 2. rewrite H_ACCESS; clear H_ACCESS H_CONT. unfold ACCESS.
    destruct (valid_block_dec m2 b); try contradiction.
    rewrite Lb. rewrite <- VB in H0.
    remember (B2 b) as q; symmetry in Heqq.
    destruct q. { split; auto. }
    remember (Mem.perm_dec m1 b ofs Max Nonempty) as t.
    destruct t. 
    { elim Pb; trivial. }
    { split; auto. }
  + intros. destruct H as [Lb Pb]. rewrite H_CONT; clear H_CONT. unfold CONT.
    destruct (valid_block_dec m2 b). 2: solve [elim n; eapply Mem.perm_valid_block; eassumption].
    rewrite Lb.
    destruct (B2 b); trivial.
    remember (Mem.perm_dec m1 b ofs Max Nonempty) as w.
    destruct w; trivial.
    rewrite <- VB in v.
    elim Pb; trivial.
    destruct (j b); trivial. }
assert (Ext12':  Mem.extends m1' m2').
{ split. 
  + (*nextblock*) rewrite NB'; trivial. 
  + (*mem_inj*)
     assert (Perm12': forall b ofs k p, Mem.perm m1' b ofs k p -> 
                                        Mem.perm m2' b ofs k p).
     { intros.
       unfold Mem.perm; rewrite H_ACCESS; clear H_ACCESS H_CONT. unfold ACCESS.
       destruct (valid_block_dec m2 b); trivial.
       remember (B2 b) as q; symmetry in Heqq; destruct q.
       - destruct (B2valid _ Heqq) as [_ RDOb2].
         destruct (RDOnly_fwd1 _ (B2_B1 _ Heqq) 1 ofs). 
         * intros. intros N. elim (RDOb2 (ofs + i)). eapply Mem.perm_extends. eassumption. eapply Mem.perm_max; eassumption.
         * eapply Mem.perm_extends. eassumption. specialize (H1 0); rewrite Zplus_0_r in H1. apply H1; [ omega | trivial].
       - remember (LS b) as w; symmetry in Heqw; destruct w.
         * remember (Mem.perm_dec m1 b ofs Max Nonempty) as t.
           destruct t; [ apply H | ].
           elim n. apply Fwd1. rewrite VB; trivial.
           eapply Mem.perm_implies. eapply Mem.perm_max. apply H. constructor.
         * remember (Mem.perm_dec m1 b ofs Max Nonempty) as t.
           destruct t; [ apply H | ].
           elim n. apply Fwd1. rewrite VB; trivial.
           eapply Mem.perm_implies. eapply Mem.perm_max. apply H. constructor. }
     split.  
       - (*mi_perm*) intros. inv H. rewrite Zplus_0_r. apply (Perm12' _ _ _ _ H0). 
       - (*mi_align*) intros. inv H. apply Z.divide_0_r. 
       - (*mi_memval *) intros. inv H. rewrite Zplus_0_r.
         rewrite H_CONT; clear H_CONT. unfold CONT.
         destruct (valid_block_dec m2 b2).
         { remember (B2 b2) as q; symmetry in Heqq; destruct q.
           + destruct (B2valid _ Heqq) as [_ RDOb2].
             destruct (RDOnly_fwd1 _ (B2_B1 _ Heqq) 1 ofs).
             * intros. intros N. elim (RDOb2 (ofs + i)). eapply Mem.perm_extends. eassumption. eapply Mem.perm_max; eassumption.
             * destruct (Mem.range_perm_loadbytes m1' b2 ofs 1) as [bytes LD]. red; intros. assert (ofs0 = ofs) by omega. subst; trivial.
               rewrite LD in H; symmetry in H.
               apply loadbytes_D in LD; simpl in LD. destruct LD as [_ BT].
               apply loadbytes_D in H; simpl in H. destruct H.
               destruct bytes. inv BT. inversion BT; clear BT. rewrite <- H4; clear H4; subst. inv H2.
               specialize (Mem.mi_memval _ _ _ (Mem.mext_inj _ _ Ext12) b2 ofs b2 0).
               rewrite Zplus_0_r; intros X; apply X; [ reflexivity | apply H; omega].
           + remember (LS b2) as w; symmetry in Heqw; destruct w.
             - remember (Mem.perm_dec m1 b2 ofs Max Nonempty) as t; destruct t.
               * clear Heqt. remember (j b2) as s; symmetry in Heqs; destruct s.
                 ++ apply memval_inject_id_refl.
                 ++ rewrite <- VB in v. destruct UnchSrc as [_ USPerm USVal].
                    apply USPerm in H0; trivial. 2: split; trivial.
                    rewrite USVal; trivial. 2: split; trivial.
                    specialize (Mem.mi_memval _  _ _ (Mem.mext_inj _ _ Ext12) b2 ofs _ _ (eq_refl _)). intros P.
                    rewrite Zplus_0_r in P. apply P; trivial.
               * rewrite <- VB in v. elim n. apply Fwd1; trivial.
                 eapply Mem.perm_max. eapply Mem.perm_implies. apply H0. constructor.
             - remember (Mem.perm_dec m1 b2 ofs Max Nonempty) as t; destruct t.
               * apply memval_inject_id_refl.
               * rewrite <- VB in v. elim n. apply Fwd1; trivial.
                 eapply Mem.perm_max. eapply Mem.perm_implies. apply H0. constructor. }
         { remember (Mem.perm_dec m1' b2 ofs Max Nonempty) as t; destruct t.
           + apply memval_inject_id_refl.
           + elim n0. eapply Mem.perm_max. eapply Mem.perm_implies. apply H0. constructor. } 
  + (*mi_perm_inv *)  
         intros. unfold Mem.perm in H. rewrite H_ACCESS in H; clear H_ACCESS H_CONT. unfold ACCESS in H.
         destruct (valid_block_dec m2 b).
         { remember (B2 b) as q; symmetry in Heqq; destruct q.
           + destruct (B2valid _ Heqq) as [_ RDOb2].
             destruct (Mem.mext_perm_inv _ _ Ext12 _ _ _ _ H).
             - left. destruct (RDOnly_fwd1 _ (B2_B1 _ Heqq) 1 ofs).
               * intros. intros N. elim (RDOb2 (ofs + i)). eapply Mem.perm_extends. eassumption. eapply Mem.perm_max; eassumption.
               * specialize (H2 0); rewrite Zplus_0_r in H2. apply H2; [ omega | trivial].
             - right. rewrite <- VB in v. intros N. apply H0. apply Fwd1; trivial.
           + remember (LS b) as w; symmetry in Heqw; destruct w.
             - remember (Mem.perm_dec m1 b ofs Max Nonempty) as t; destruct t.
               * left; trivial.
               * right. rewrite <- VB in v. intros N. apply n. apply Fwd1; trivial.
             - remember (Mem.perm_dec m1 b ofs Max Nonempty) as t; destruct t.
               * left; trivial.
               * right. rewrite <- VB in v. intros N. apply n. apply Fwd1; trivial. }
         { left; trivial. } } 
assert (Inj23': Mem.inject j' m2' m3').
{ assert (MI: Mem.mem_inj j' m2' m3').
  { assert (MiPerm: forall b1 b2 delta ofs k p,  j' b1 = Some (b2, delta) ->
                       Mem.perm m2' b1 ofs k p -> 
                       Mem.perm m3' b2 (ofs + delta) k p).
    + intros b2 b3; intros.
      assert (NP: Mem.perm m2' b2 ofs Max Nonempty).
      { eapply Mem.perm_max. eapply Mem.perm_implies. apply H0. constructor. }
      unfold Mem.perm in H0; rewrite H_ACCESS in H0; unfold ACCESS in H0.
      unfold Mem.perm in NP; rewrite H_ACCESS in NP; unfold ACCESS in NP.
      destruct (valid_block_dec m2 b2).
      { assert (Val1: Mem.valid_block m1 b2) by (rewrite VB; trivial).
        remember (B2 b2) as q; symmetry in Heqq; destruct q.
        + destruct (B2valid _ Heqq) as [_ RDOb2].
          remember (j b2) as w; symmetry in Heqw; destruct w.
          - destruct p0. rewrite (INC _ _ _ Heqw) in H; inv H.
            destruct (RDOnly_fwd3 _ (B2_B3 _ _ _ Heqw Heqq) 1 (ofs + delta)).
               * intros i I N. replace (ofs + delta + i) with (ofs+delta) in N by omega.
                 destruct (Mem.mi_perm_inv _ _ _ Inj23 b2 ofs b3 delta Cur Writable Heqw N) as [A | A]; [ | contradiction].
                 apply Mem.perm_max in A; apply (RDOb2 _ A).
               * specialize (H1 0); rewrite Zplus_0_r in H1. apply H1. omega. eapply Inj23; eassumption.
          - destruct (ESEP _ _ _ Heqw H) as [A _]; contradiction.
        + remember (LS b2) as w; symmetry in Heqw; destruct w.
          - remember (Mem.perm_dec m1 b2 ofs Max Nonempty) as  t; destruct t.
            * clear Heqt. eapply Inj13'; eassumption.
            * remember (j b2) as s; symmetry in Heqs; destruct s.
              ++ destruct p0. specialize (INC _ _ _ Heqs). rewrite INC in H; inv H.
                 eapply UnchTgt.
                 -- split. rewrite <- (local _ _ _ Heqs); trivial.
                    red; intros. intros N. 
                    destruct (eq_block b0 b2).
                    ** subst. rewrite H in Heqs; inv Heqs.
                       assert (A:ofs + delta - delta = ofs) by omega.
                       rewrite A in N; contradiction.
                    ** apply (Mem.perm_extends _ _ _ _ _ _ Ext12) in N.
                       destruct (Mem.mi_no_overlap _ _ _ Inj23 _ _ _ _ _ _ _ _ n0 H Heqs N NP).
                       congruence. omega.
                 -- eapply Inj23; eassumption.
                 -- eapply Inj23; eassumption.
              ++ destruct (ESEP _ _ _ Heqs H); congruence.
          - remember (Mem.perm_dec m1 b2 ofs Max Nonempty) as t; destruct t; [eapply Inj13'; eassumption | contradiction].
      }
      { eapply Inj13'; eassumption. }
   + split; trivial. 
     - intros b2 b3; intros. red in H0. unfold Mem.perm in H0. rewrite H_ACCESS in H0. unfold ACCESS in H0.
       destruct (valid_block_dec m2 b2).
       { assert (Val1: Mem.valid_block m1 b2) by (rewrite VB; trivial).
         remember (B2 b2) as q; symmetry in Heqq; destruct q.
         + remember (j b2) as w; symmetry in Heqw; destruct w.
          - destruct p0. rewrite (INC _ _ _ Heqw) in H; inv H. eapply Inj23. eassumption. red; intros. apply H0. apply H.
          - destruct (ESEP _ _ _ Heqw H) as [A _]; contradiction.
         + remember (LS b2) as w; symmetry in Heqw; destruct w.
           - remember (j b2) as s; symmetry in Heqs; destruct s.
              ++ destruct p0. specialize (INC _ _ _ Heqs). rewrite INC in H; inv H.
                 eapply Inj23. eassumption.
                 red; intros. specialize (H0 _ H).
                 destruct (Mem.perm_dec m1 b2 ofs0 Max Nonempty).
                 -- eapply Mem.perm_extends; eassumption.
                 -- eapply Mem.perm_implies. eassumption. constructor.
              ++ destruct (ESEP _ _ _ Heqs H). congruence.
           - eapply Inj13'; [eassumption | red; intros].
             specialize (H0 _ H1).
             destruct (Mem.perm_dec m1 b2 ofs0 Max Nonempty); [ apply H0 | contradiction]. }
       { eapply Inj13'; eassumption. }
     - intros b2 ofs b3; intros.
       unfold Mem.perm in H0; rewrite H_ACCESS in H0. unfold ACCESS in H0.
       rewrite H_CONT; clear H_CONT H_ACCESS. unfold CONT.
       destruct (valid_block_dec m2 b2).
       { assert (Val1: Mem.valid_block m1 b2) by (rewrite VB; trivial).
         remember (B2 b2) as q; symmetry in Heqq; destruct q.
         + destruct (B2valid _ Heqq) as [_ RDOb2].
           remember (j b2) as w; symmetry in Heqw; destruct w.
           - destruct p. rewrite (INC _ _ _ Heqw) in H; inv H.
             destruct (RDOnly_fwd3 _ (B2_B3 _ _ _ Heqw Heqq) 1 (ofs + delta)).
               * intros i I N. replace (ofs + delta + i) with (ofs+delta) in N by omega.
                 destruct (Mem.mi_perm_inv _ _ _ Inj23 b2 ofs b3 delta Cur Writable Heqw N) as [A | A].
                 apply Mem.perm_max in A; apply (RDOb2 _ A). 
                 apply Mem.perm_max in H0. apply A. eapply Mem.perm_implies. apply H0. constructor. 
               * destruct (Mem.range_perm_loadbytes m3' b3 (ofs+delta) 1) as [bytes Bytes].
                 ++ red; intros. specialize (H1 0); rewrite Zplus_0_r in H1.
                    replace ofs0 with (ofs+delta) by omega. apply H1. omega. eapply Inj23; eauto.
                 ++ rewrite Bytes in H; symmetry in H. 
                    apply loadbytes_D in Bytes; simpl in Bytes; destruct Bytes.
                    apply loadbytes_D in H; simpl in H; destruct H. 
                    destruct bytes. discriminate. inversion H3; clear H3. inversion H4; clear H4. rewrite <- H6, H5; subst.
                    eapply memval_inject_incr; eauto. apply Inj23; eassumption.
           - destruct (ESEP _ _ _ Heqw H); congruence.
         + remember (LS b2) as w; symmetry in Heqw; destruct w.
           - destruct (Mem.perm_dec m1 b2 ofs Max Nonempty).
             * remember (j b2) as s; symmetry in Heqs; destruct s.
               ++ destruct p0. apply Inj13'; eassumption.
               ++ destruct (ESEP _ _ _ Heqs H). congruence.
             * remember (j b2) as s; symmetry in Heqs; destruct s.
               ++ destruct p. rewrite (INC _ _ _ Heqs) in H; inv H.
                  destruct UnchTgt. rewrite unchanged_on_contents.
                    eapply memval_inject_incr; try eassumption.
                    apply Inj23; eassumption.
                    split. rewrite <- (local _ _ _ Heqs); trivial.
                    red; intros. intros N.
                    destruct (eq_block b0 b2); subst.
                    -- rewrite H in Heqs; inv Heqs. replace (ofs + delta - delta) with ofs in N by omega; contradiction.
                    -- destruct (Mem.mi_no_overlap j _ _ Inj23 b0 b3 delta0 b2 b3 delta (ofs + delta - delta0) ofs); trivial.
                         eapply Mem.perm_extends; eassumption.
                         eapply Mem.perm_max. eapply Mem.perm_implies. eassumption. constructor.
                       congruence. omega.
                   -- eapply Inj23; eassumption.
               ++ destruct (ESEP _ _ _ Heqs H). congruence.
           - destruct (Mem.perm_dec m1 b2 ofs Max Nonempty); try contradiction.
             eapply Inj13'; eassumption. }
       { destruct (Mem.perm_dec m1' b2 ofs Max Nonempty).
             eapply Inj13'; eassumption. 
         elim n0. eapply Mem.perm_max. eapply Mem.perm_implies. eassumption. constructor. } }
   split; trivial; try eapply Inj13'.
   + intros. apply Inj13'. intros N. rewrite VB' in N. apply (H N).
   + red; intros. 
     unfold Mem.perm in H2. rewrite H_ACCESS in H2. unfold ACCESS in H2. 
     unfold Mem.perm in H3. rewrite H_ACCESS in H3. unfold ACCESS in H3.
     clear H_ACCESS H_CONT.
     remember (j b1) as Jb1; symmetry in HeqJb1; destruct Jb1.
     - destruct p. assert (jj_b1 := INC _ _ _ HeqJb1). rewrite H0 in jj_b1; inv jj_b1.
       destruct (valid_block_dec m2 b1).
       Focus 2. elim n. eapply Mem.valid_block_inject_1. apply HeqJb1. eassumption.
       remember (j b2) as Jb2; symmetry in HeqJb2; destruct Jb2.
       * destruct p. assert (jj_b2 := INC _ _ _ HeqJb2). rewrite H1 in jj_b2; inv jj_b2.
         destruct (valid_block_dec m2 b2).
         Focus 2. elim n. eapply Mem.valid_block_inject_1. apply HeqJb2. eassumption.
         remember (B2 b1) as q1; symmetry in Heqq1; destruct q1; 
         remember (B2 b2) as q2; symmetry in Heqq2; destruct q2. 
         ++ eapply Inj23; eassumption.
         ++ remember (LS b2) as w2; symmetry in Heqw2; destruct w2.
            -- destruct (Mem.perm_dec m1 b2 ofs2 Max Nonempty).
               ** eapply Inj23; try eassumption. eapply Mem.perm_extends; eassumption.
               ** eapply Inj23; try eassumption.
            -- destruct (Mem.perm_dec m1 b2 ofs2 Max Nonempty); try contradiction.
               eapply Inj23; try eassumption. eapply Mem.perm_extends; eassumption.
         ++ remember (LS b1) as w1; symmetry in Heqw1; destruct w1.
            -- destruct (Mem.perm_dec m1 b1 ofs1 Max Nonempty).
               ** eapply Inj23; try eassumption. eapply Mem.perm_extends; eassumption.
               ** eapply Inj23; try eassumption.
            -- destruct (Mem.perm_dec m1 b1 ofs1 Max Nonempty); try contradiction.
               eapply Inj23; try eassumption. eapply Mem.perm_extends; eassumption.
         ++ remember (LS b1) as w1; symmetry in Heqw1; destruct w1;
            remember (LS b2) as w2; symmetry in Heqw2; destruct w2.
            -- destruct (Mem.perm_dec m1 b1 ofs1 Max Nonempty);
               destruct (Mem.perm_dec m1 b2 ofs2 Max Nonempty).
               ** eapply Inj23; try eassumption. eapply Mem.perm_extends; eassumption. eapply Mem.perm_extends; eassumption.
               ** eapply Inj23; try eassumption. eapply Mem.perm_extends; eassumption.
               ** eapply Inj23; try eassumption. eapply Mem.perm_extends; eassumption.
               ** eapply Inj23; try eassumption.
            -- destruct (Mem.perm_dec m1 b1 ofs1 Max Nonempty); 
               destruct (Mem.perm_dec m1 b2 ofs2 Max Nonempty); try contradiction.
               ** eapply Inj23; try eassumption. eapply Mem.perm_extends; eassumption. eapply Mem.perm_extends; eassumption.
               ** eapply Inj23; try eassumption. eapply Mem.perm_extends; eassumption.
            -- destruct (Mem.perm_dec m1 b1 ofs1 Max Nonempty); 
               destruct (Mem.perm_dec m1 b2 ofs2 Max Nonempty); try contradiction.
               ** eapply Inj23; try eassumption. eapply Mem.perm_extends; eassumption. eapply Mem.perm_extends; eassumption.
               ** eapply Inj23; try eassumption. eapply Mem.perm_extends; eassumption.
            -- destruct (Mem.perm_dec m1 b1 ofs1 Max Nonempty); 
               destruct (Mem.perm_dec m1 b2 ofs2 Max Nonempty); try contradiction.
               ** eapply Inj23; try eassumption. eapply Mem.perm_extends; eassumption. eapply Mem.perm_extends; eassumption.
       * destruct (ESEP _ _ _ HeqJb2 H1) as [AA BB].
         destruct (valid_block_dec m2 b2); [ contradiction |  clear AA].
         destruct (eq_block b b2'); [ subst b2' | left; trivial].
         rewrite (local _ _ _ HeqJb1), BB in H2; [clear BB | eapply (JValid _ _ _ HeqJb1)].
         specialize (Gsep _ _ _ HeqJb2 H1).
         remember (B2 b1) as q2; symmetry in Heqq2; destruct q2.
         ++ destruct (B2valid _ Heqq2) as [_ RDOb1].
            rewrite (B2_B3 _ _ _ HeqJb1 Heqq2) in Gsep; discriminate.
         ++ destruct (Mem.perm_dec m1 b1 ofs1 Max Nonempty); [ eapply Inj13'; eassumption | contradiction].
     - destruct (ESEP _ _ _ HeqJb1 H0).
       destruct (valid_block_dec m2 b1); [ contradiction | clear H4].
       destruct (valid_block_dec m2 b2); [ | eapply Inj13'; eassumption].
       remember (j b2) as a; symmetry in Heqa; destruct a; [destruct p | destruct (ESEP _ _ _ Heqa H1); contradiction].
       specialize (INC _ _ _ Heqa); rewrite H1 in INC; inv INC.
       destruct (JValid _ _ _ Heqa) as [_ VBb].
       rewrite (local _ _ _ Heqa) in H3.
       remember (B2 b2) as q1; symmetry in Heqq1; destruct q1.
       { destruct (eq_block b1' b); [ subst b1' | left; trivial].
         specialize (B2_B3 _ _ _ Heqa Heqq1).
         specialize (Gsep _ _ _ HeqJb1 H0); congruence. }
       destruct (Mem.perm_dec m1 b2 ofs2 Max Nonempty).
       ++ eapply Inj13'; try eassumption. destruct (LT b); eassumption.
       ++ remember (LT b) as p; destruct p; [symmetry in Heqp | contradiction].
          destruct (eq_block b1' b); [ subst b1' | left; trivial].
          rewrite (H5 VBb) in Heqp; discriminate.
   + intros. unfold Mem.perm in H0. rewrite H_ACCESS in H0. unfold ACCESS in H0.
     remember (j b) as jb; symmetry in Heqjb; destruct jb.
     - destruct p. specialize (INC _ _ _ Heqjb). rewrite INC in H; inv H.
       destruct (valid_block_dec m2 b).
       { destruct (B2 b).
         + eapply Inj23; eassumption.
         + destruct (LS b).
           - destruct (Mem.perm_dec m1 b (Ptrofs.unsigned ofs) Max Nonempty);
             destruct (Mem.perm_dec m1 b (Ptrofs.unsigned ofs - 1) Max Nonempty).
             * eapply Inj13'; eassumption.
             * eapply Inj23; try eassumption. left. eapply Mem.perm_extends; eassumption.
             * eapply Inj23; try eassumption. right. eapply Mem.perm_extends; eassumption.
             * eapply Inj23; eassumption.
           - destruct (Mem.perm_dec m1 b (Ptrofs.unsigned ofs) Max Nonempty);
             destruct (Mem.perm_dec m1 b (Ptrofs.unsigned ofs - 1) Max Nonempty).
             * eapply Inj13'; eassumption.
             * eapply Inj23; try eassumption. left. eapply Mem.perm_extends; eassumption.
             * eapply Inj23; try eassumption. right. eapply Mem.perm_extends; eassumption.
             * destruct H0; contradiction. }
       { eapply Inj13'; eassumption. }
    - destruct (ESEP _ _ _ Heqjb H) as [AA BB]. 
       destruct (valid_block_dec m2 b); try contradiction. 
       { eapply Inj13'; eassumption. }
  + (*perm_inv*)
    intros b2 ofs b3; intros. destruct (Mem.mi_perm_inv _ _ _ Inj13' _ _ _ _ _ _ H H0).
    left. eapply Mem.perm_extends; eassumption.
    destruct (Mem.perm_dec m2' b2 ofs Max Nonempty). 2: right; trivial. left.
    unfold Mem.perm in p0. rewrite H_ACCESS in p0. unfold ACCESS in p0.
    unfold Mem.perm. rewrite H_ACCESS. unfold ACCESS. clear H_ACCESS H_CONT.
    remember (j b2) as s; symmetry in Heqs; destruct s.
    { destruct p1.
      rewrite (INC _ _ _ Heqs) in H; inv H.
      destruct (JValid _ _ _ Heqs).
      destruct (valid_block_dec m2 b2); try contradiction.
      remember (B2 b2) as q; symmetry in Heqq; destruct q.
      + destruct (B2valid _ Heqq) as [_ RDOb2].
        destruct (RDOnly_fwd3 _ (B2_B3 _ _ _ Heqs Heqq) 1 (ofs+delta)).
        - intros i I N. replace (ofs+delta+i) with (ofs+delta) in N by omega.
          eapply Inj23 in N; [ destruct N as [N | N] | eassumption]. apply Mem.perm_max in N. apply (RDOb2 _ N). contradiction.
        - specialize (H4 0). rewrite Zplus_0_r in H4. apply H4 in H0; [clear H4 | omega].
          eapply Inj23 in H0; [ destruct H0 as [N | N] | eassumption]. trivial. contradiction.
      + remember (LS b2) as w; symmetry in Heqw; destruct w.
        - destruct (Mem.perm_dec m1 b2 ofs Max Nonempty). contradiction.
          destruct UnchTgt as [_ UP _].
          apply UP in H0.
          * destruct (Mem.mi_perm_inv _ _ _ Inj23 _ _ _ _ _ _ Heqs H0); trivial. contradiction.
          * split. rewrite <- (local _ _ _ Heqs); trivial.
            red; intros. destruct (eq_block b0 b2).
            ++ subst. rewrite H4 in Heqs; inv Heqs. replace (ofs + delta-delta) with ofs by omega; trivial.
            ++ intros N. eapply Mem.perm_extends in N. 2: eassumption.
                 destruct (Mem.mi_no_overlap _ _ _ Inj23 _ _ _ _ _ _ _ _ n0 H4 Heqs N p0).
                 congruence. omega.
          * eapply Inj23; eassumption.
        - destruct (Mem.perm_dec m1 b2 ofs Max Nonempty); contradiction. }
    { destruct (ESEP _ _ _ Heqs H) as [AA BB].
      destruct (valid_block_dec m2 b2); try contradiction. } }
intuition.
Qed.
End Interpolation_EI.