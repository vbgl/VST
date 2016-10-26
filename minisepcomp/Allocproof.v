(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Correctness proof for the [Allocation] pass (validated translation from
  RTL to LTL). *)

Require Import FSets.
Require Import Coqlib minisepcomp.Ordered Maps Errors Integers Floats.
Require Import AST Linking minisepcomp.Lattice minisepcomp.Kildall.
Require Import Values Memory Globalenvs Events Smallstep.
Require Archi.
Require Import minisepcomp.Op minisepcomp.Registers minisepcomp.RTL_memsem minisepcomp.Locations minisepcomp.Conventions minisepcomp.RTLtyping minisepcomp.LTL_memsem.
Require Import minisepcomp.Allocation.

Require Import sepcomp.mem_lemmas.
Require Import sepcomp.semantics.
Require Import sepcomp.semantics_lemmas.
Require Import sepcomp.effect_semantics.
Require Import minisepcomp.mini_simulations.
Require Import minisepcomp.mini_simulations_lemmas.

Require Import minisepcomp.val_casted.

Definition match_prog (p: RTL_memsem.program) (tp: LTL_memsem.program) :=
  match_program (fun _ f tf => transf_fundef f = OK tf) eq p tp.

Lemma transf_program_match:
  forall p tp, transf_program p = OK tp -> match_prog p tp.
Proof.
  intros. eapply match_transform_partial_program; eauto.
Qed.

(** * Soundness of structural checks *)

Definition expand_move (sd: loc * loc) : instruction :=
  match sd with
  | (R src, R dst) => Lop Omove (src::nil) dst
  | (S sl ofs ty, R dst) => Lgetstack sl ofs ty dst
  | (R src, S sl ofs ty) => Lsetstack src sl ofs ty
  | (S _ _ _, S _ _ _) => Lreturn    (**r should never happen *)
  end.

Definition expand_moves (mv: moves) (k: bblock) : bblock :=
  List.map expand_move mv ++ k.

Definition wf_move (sd: loc * loc) : Prop :=
  match sd with
  | (S _ _ _, S _ _ _) => False
  | _ => True
  end.

Definition wf_moves (mv: moves) : Prop :=
  forall sd, In sd mv -> wf_move sd.

Inductive expand_block_shape: block_shape -> RTL_memsem.instruction -> LTL_memsem.bblock -> Prop :=
  | ebs_nop: forall mv s k,
      wf_moves mv ->
      expand_block_shape (BSnop mv s)
                         (Inop s)
                         (expand_moves mv (Lbranch s :: k))
  | ebs_move: forall src dst mv s k,
      wf_moves mv ->
      expand_block_shape (BSmove src dst mv s)
                         (Iop Omove (src :: nil) dst s)
                         (expand_moves mv (Lbranch s :: k))
  | ebs_makelong: forall src1 src2 dst mv s k,
      wf_moves mv ->
      expand_block_shape (BSmakelong src1 src2 dst mv s)
                         (Iop Omakelong (src1 :: src2 :: nil) dst s)
                         (expand_moves mv (Lbranch s :: k))
  | ebs_lowlong: forall src dst mv s k,
      wf_moves mv ->
      expand_block_shape (BSlowlong src dst mv s)
                         (Iop Olowlong (src :: nil) dst s)
                         (expand_moves mv (Lbranch s :: k))
  | ebs_highlong: forall src dst mv s k,
      wf_moves mv ->
      expand_block_shape (BShighlong src dst mv s)
                         (Iop Ohighlong (src :: nil) dst s)
                         (expand_moves mv (Lbranch s :: k))
  | ebs_op: forall op args res mv1 args' res' mv2 s k,
      wf_moves mv1 -> wf_moves mv2 ->
      expand_block_shape (BSop op args res mv1 args' res' mv2 s)
                         (Iop op args res s)
                         (expand_moves mv1
                           (Lop op args' res' :: expand_moves mv2 (Lbranch s :: k)))
  | ebs_op_dead: forall op args res mv s k,
      wf_moves mv ->
      expand_block_shape (BSopdead op args res mv s)
                         (Iop op args res s)
                         (expand_moves mv (Lbranch s :: k))
  | ebs_load: forall chunk addr args dst mv1 args' dst' mv2 s k,
      wf_moves mv1 -> wf_moves mv2 ->
      expand_block_shape (BSload chunk addr args dst mv1 args' dst' mv2 s)
                         (Iload chunk addr args dst s)
                         (expand_moves mv1
                           (Lload chunk addr args' dst' :: expand_moves mv2 (Lbranch s :: k)))
  | ebs_load2: forall addr addr2 args dst mv1 args1' dst1' mv2 args2' dst2' mv3 s k,
      wf_moves mv1 -> wf_moves mv2 -> wf_moves mv3 ->
      offset_addressing addr (Int.repr 4) = Some addr2 ->
      expand_block_shape (BSload2 addr addr2 args dst mv1 args1' dst1' mv2 args2' dst2' mv3 s)
                         (Iload Mint64 addr args dst s)
                         (expand_moves mv1
                           (Lload Mint32 addr args1' dst1' ::
                           expand_moves mv2
                             (Lload Mint32 addr2 args2' dst2' ::
                              expand_moves mv3 (Lbranch s :: k))))
  | ebs_load2_1: forall addr args dst mv1 args' dst' mv2 s k,
      wf_moves mv1 -> wf_moves mv2 ->
      expand_block_shape (BSload2_1 addr args dst mv1 args' dst' mv2 s)
                         (Iload Mint64 addr args dst s)
                         (expand_moves mv1
                           (Lload Mint32 addr args' dst' ::
                            expand_moves mv2 (Lbranch s :: k)))
  | ebs_load2_2: forall addr addr2 args dst mv1 args' dst' mv2 s k,
      wf_moves mv1 -> wf_moves mv2 ->
      offset_addressing addr (Int.repr 4) = Some addr2 ->
      expand_block_shape (BSload2_2 addr addr2 args dst mv1 args' dst' mv2 s)
                         (Iload Mint64 addr args dst s)
                         (expand_moves mv1
                           (Lload Mint32 addr2 args' dst' ::
                            expand_moves mv2 (Lbranch s :: k)))
  | ebs_load_dead: forall chunk addr args dst mv s k,
      wf_moves mv ->
      expand_block_shape (BSloaddead chunk addr args dst mv s)
                         (Iload chunk addr args dst s)
                         (expand_moves mv (Lbranch s :: k))
  | ebs_store: forall chunk addr args src mv1 args' src' s k,
      wf_moves mv1 ->
      expand_block_shape (BSstore chunk addr args src mv1 args' src' s)
                         (Istore chunk addr args src s)
                         (expand_moves mv1
                           (Lstore chunk addr args' src' :: Lbranch s :: k))
  | ebs_store2: forall addr addr2 args src mv1 args1' src1' mv2 args2' src2' s k,
      wf_moves mv1 -> wf_moves mv2 ->
      offset_addressing addr (Int.repr 4) = Some addr2 ->
      expand_block_shape (BSstore2 addr addr2 args src mv1 args1' src1' mv2 args2' src2' s)
                         (Istore Mint64 addr args src s)
                         (expand_moves mv1
                           (Lstore Mint32 addr args1' src1' ::
                            expand_moves mv2
                             (Lstore Mint32 addr2 args2' src2' ::
                              Lbranch s :: k)))
  | ebs_call: forall sg ros args res mv1 ros' mv2 s k,
      wf_moves mv1 -> wf_moves mv2 ->
      expand_block_shape (BScall sg ros args res mv1 ros' mv2 s)
                         (Icall sg ros args res s)
                         (expand_moves mv1
                           (Lcall sg ros' :: expand_moves mv2 (Lbranch s :: k)))
  | ebs_tailcall: forall sg ros args mv ros' k,
      wf_moves mv ->
      expand_block_shape (BStailcall sg ros args mv ros')
                         (Itailcall sg ros args)
                         (expand_moves mv (Ltailcall sg ros' :: k))
  | ebs_builtin: forall ef args res mv1 args' res' mv2 s k,
      wf_moves mv1 -> wf_moves mv2 ->
      expand_block_shape (BSbuiltin ef args res mv1 args' res' mv2 s)
                         (Ibuiltin ef args res s)
                         (expand_moves mv1
                           (Lbuiltin ef args' res' :: expand_moves mv2 (Lbranch s :: k)))
  | ebs_cond: forall cond args mv args' s1 s2 k,
      wf_moves mv ->
      expand_block_shape (BScond cond args mv args' s1 s2)
                         (Icond cond args s1 s2)
                         (expand_moves mv (Lcond cond args' s1 s2 :: k))
  | ebs_jumptable: forall arg mv arg' tbl k,
      wf_moves mv ->
      expand_block_shape (BSjumptable arg mv arg' tbl)
                         (Ijumptable arg tbl)
                         (expand_moves mv (Ljumptable arg' tbl :: k))
  | ebs_return: forall optarg mv k,
      wf_moves mv ->
      expand_block_shape (BSreturn optarg mv)
                         (Ireturn optarg)
                         (expand_moves mv (Lreturn :: k)).

Ltac MonadInv :=
  match goal with
  | [ H: match ?x with Some _ => _ | None => None end = Some _ |- _ ] =>
        destruct x as [] eqn:? ; [MonadInv|discriminate]
  | [ H: match ?x with left _ => _ | right _ => None end = Some _ |- _ ] =>
        destruct x; [MonadInv|discriminate]
  | [ H: match negb (proj_sumbool ?x) with true => _ | false => None end = Some _ |- _ ] =>
        destruct x; [discriminate|simpl in H; MonadInv]
  | [ H: match negb ?x with true => _ | false => None end = Some _ |- _ ] =>
        destruct x; [discriminate|simpl in H; MonadInv]
  | [ H: match ?x with true => _ | false => None end = Some _ |- _ ] =>
        destruct x as [] eqn:? ; [MonadInv|discriminate]
  | [ H: match ?x with (_, _) => _ end = Some _ |- _ ] =>
        destruct x as [] eqn:? ; MonadInv
  | [ H: Some _ = Some _ |- _ ] =>
        inv H; MonadInv
  | [ H: None = Some _ |- _ ] =>
        discriminate
  | _ =>
        idtac
  end.

Lemma extract_moves_sound:
  forall b mv b',
  extract_moves nil b = (mv, b') ->
  wf_moves mv /\ b = expand_moves mv b'.
Proof.
  assert (BASE:
      forall accu b,
      wf_moves accu ->
      wf_moves (List.rev accu) /\ expand_moves (List.rev accu) b = expand_moves (List.rev accu) b).
   intros; split; auto.
   red; intros. apply H. rewrite <- in_rev in H0; auto.

  assert (IND: forall b accu mv b',
          extract_moves accu b = (mv, b') ->
          wf_moves accu ->
          wf_moves mv /\ expand_moves (List.rev accu) b = expand_moves mv b').
    induction b; simpl; intros.
    inv H. auto.
    destruct a; try (inv H; apply BASE; auto; fail).
    destruct (is_move_operation op args) as [arg|] eqn:E.
    exploit is_move_operation_correct; eauto. intros [A B]; subst.
    (* reg-reg move *)
    exploit IHb; eauto.
      red; intros. destruct H1; auto. subst sd; exact I.
    intros [P Q].
    split; auto. rewrite <- Q. simpl. unfold expand_moves. rewrite map_app.
    rewrite app_ass. simpl. auto.
    inv H; apply BASE; auto.
    (* stack-reg move *)
    exploit IHb; eauto.
      red; intros. destruct H1; auto. subst sd; exact I.
    intros [P Q].
    split; auto. rewrite <- Q. simpl. unfold expand_moves. rewrite map_app.
    rewrite app_ass. simpl. auto.
    (* reg-stack move *)
    exploit IHb; eauto.
      red; intros. destruct H1; auto. subst sd; exact I.
    intros [P Q].
    split; auto. rewrite <- Q. simpl. unfold expand_moves. rewrite map_app.
    rewrite app_ass. simpl. auto.

  intros. exploit IND; eauto. red; intros. elim H0.
Qed.

Lemma check_succ_sound:
  forall s b, check_succ s b = true -> exists k, b = Lbranch s :: k.
Proof.
  intros. destruct b; simpl in H; try discriminate.
  destruct i; try discriminate.
  destruct (peq s s0); simpl in H; inv H. exists b; auto.
Qed.

Ltac UseParsingLemmas :=
  match goal with
  | [ H: extract_moves nil _ = (_, _) |- _ ] =>
      destruct (extract_moves_sound _ _ _ H); clear H; subst; UseParsingLemmas
  | [ H: check_succ _ _ = true |- _ ] =>
      try discriminate;
      destruct (check_succ_sound _ _ H); clear H; subst; UseParsingLemmas
  | _ => idtac
  end.

Lemma pair_instr_block_sound:
  forall i b bsh,
  pair_instr_block i b = Some bsh -> expand_block_shape bsh i b.
Proof.
  intros; destruct i; simpl in H; MonadInv; UseParsingLemmas.
(* nop *)
  econstructor; eauto.
(* op *)
  destruct (classify_operation o l).
  (* move *)
  MonadInv; UseParsingLemmas. econstructor; eauto.
  (* makelong *)
  MonadInv; UseParsingLemmas. econstructor; eauto.
  (* lowlong *)
  MonadInv; UseParsingLemmas. econstructor; eauto.
  (* highlong *)
  MonadInv; UseParsingLemmas. econstructor; eauto.
  (* other ops *)
  MonadInv. destruct b0.
  MonadInv; UseParsingLemmas.
  destruct i; MonadInv; UseParsingLemmas.
  eapply ebs_op; eauto.
  inv H0. eapply ebs_op_dead; eauto.
(* load *)
  destruct b0.
  MonadInv; UseParsingLemmas.
  destruct i; MonadInv; UseParsingLemmas.
  destruct (chunk_eq m Mint64).
  MonadInv; UseParsingLemmas.
  destruct b; MonadInv; UseParsingLemmas. destruct i; MonadInv; UseParsingLemmas.
  eapply ebs_load2; eauto.
  destruct (eq_addressing a addr).
  MonadInv. inv H2. eapply ebs_load2_1; eauto.
  MonadInv. inv H2. eapply ebs_load2_2; eauto.
  MonadInv; UseParsingLemmas. eapply ebs_load; eauto.
  inv H. eapply ebs_load_dead; eauto.
(* store *)
  destruct b0; MonadInv. destruct i; MonadInv; UseParsingLemmas.
  destruct (chunk_eq m Mint64).
  MonadInv; UseParsingLemmas.
  destruct b; MonadInv. destruct i; MonadInv; UseParsingLemmas.
  eapply ebs_store2; eauto.
  MonadInv; UseParsingLemmas.
  eapply ebs_store; eauto.
(* call *)
  destruct b0; MonadInv. destruct i; MonadInv; UseParsingLemmas. econstructor; eauto.
(* tailcall *)
  destruct b0; MonadInv. destruct i; MonadInv; UseParsingLemmas. econstructor; eauto.
(* builtin *)
  destruct b1; MonadInv. destruct i; MonadInv; UseParsingLemmas.
  econstructor; eauto.
(* cond *)
  destruct b0; MonadInv. destruct i; MonadInv; UseParsingLemmas. econstructor; eauto.
(* jumptable *)
  destruct b0; MonadInv. destruct i; MonadInv; UseParsingLemmas. econstructor; eauto.
(* return *)
  destruct b0; MonadInv. destruct i; MonadInv; UseParsingLemmas. econstructor; eauto.
Qed.

Lemma matching_instr_block:
  forall f1 f2 pc bsh i,
  (pair_codes f1 f2)!pc = Some bsh ->
  (RTL_memsem.fn_code f1)!pc = Some i ->
  exists b, (LTL_memsem.fn_code f2)!pc = Some b /\ expand_block_shape bsh i b.
Proof.
  intros. unfold pair_codes in H. rewrite PTree.gcombine in H; auto. rewrite H0 in H.
  destruct (LTL_memsem.fn_code f2)!pc as [b|].
  exists b; split; auto. apply pair_instr_block_sound; auto.
  discriminate.
Qed.

(** * Properties of equations *)

Module ESF := FSetFacts.Facts(EqSet).
Module ESP := FSetProperties.Properties(EqSet).
Module ESD := FSetDecide.Decide(EqSet).

Definition sel_val (k: equation_kind) (v: val) : val :=
  match k with
  | Full => v
  | Low => Val.loword v
  | High => Val.hiword v
  end.

(** A set of equations [e] is satisfied in a RTL pseudoreg state [rs]
  and an LTL location state [ls] if, for every equation [r = l [k]] in [e],
  [sel_val k (rs#r)] (the [k] fragment of [r]'s value in the RTL code)
  is less defined than [ls l] (the value of [l] in the LTL code). *)

Definition satisf (rs: regset) (ls: locset) (e: eqs) : Prop :=
  forall q, EqSet.In q e -> Val.lessdef (sel_val (ekind q) rs#(ereg q)) (ls (eloc q)).

Lemma empty_eqs_satisf:
  forall rs ls, satisf rs ls empty_eqs.
Proof.
  unfold empty_eqs; intros; red; intros. ESD.fsetdec.
Qed.

Lemma satisf_incr:
  forall rs ls (e1 e2: eqs),
  satisf rs ls e2 -> EqSet.Subset e1 e2 -> satisf rs ls e1.
Proof.
  unfold satisf; intros. apply H. ESD.fsetdec.
Qed.

Lemma satisf_undef_reg:
  forall rs ls e r,
  satisf rs ls e ->
  satisf (rs#r <- Vundef) ls e.
Proof.
  intros; red; intros. rewrite Regmap.gsspec. destruct (peq (ereg q) r); auto.
  destruct (ekind q); simpl; auto.
Qed.

Lemma add_equation_lessdef:
  forall rs ls q e,
  satisf rs ls (add_equation q e) -> Val.lessdef (sel_val (ekind q) rs#(ereg q)) (ls (eloc q)).
Proof.
  intros. apply H. unfold add_equation. simpl. apply EqSet.add_1. auto.
Qed.

Lemma add_equation_satisf:
  forall rs ls q e,
  satisf rs ls (add_equation q e) -> satisf rs ls e.
Proof.
  intros. eapply satisf_incr; eauto. unfold add_equation. simpl. ESD.fsetdec.
Qed.

Lemma add_equations_satisf:
  forall rs ls rl ml e e',
  add_equations rl ml e = Some e' ->
  satisf rs ls e' -> satisf rs ls e.
Proof.
  induction rl; destruct ml; simpl; intros; MonadInv.
  auto.
  eapply add_equation_satisf; eauto.
Qed.

Lemma add_equations_lessdef:
  forall rs ls rl ml e e',
  add_equations rl ml e = Some e' ->
  satisf rs ls e' ->
  Val.lessdef_list (rs##rl) (reglist ls ml).
Proof.
  induction rl; destruct ml; simpl; intros; MonadInv.
  constructor.
  constructor; eauto.
  apply add_equation_lessdef with (e := e) (q := Eq Full a (R m)).
  eapply add_equations_satisf; eauto.
Qed.

Lemma add_equations_args_satisf:
  forall rs ls rl tyl ll e e',
  add_equations_args rl tyl ll e = Some e' ->
  satisf rs ls e' -> satisf rs ls e.
Proof.
  intros until e'. functional induction (add_equations_args rl tyl ll e); intros.
- inv H; auto.
- eapply add_equation_satisf; eauto.
- eapply add_equation_satisf. eapply add_equation_satisf. eauto.
- congruence.
Qed.

Lemma val_longofwords_eq:
  forall v,
  Val.has_type v Tlong ->
  Val.longofwords (Val.hiword v) (Val.loword v) = v.
Proof.
  intros. red in H. destruct v; try contradiction.
  reflexivity.
  simpl. rewrite Int64.ofwords_recompose. auto.
Qed.

Lemma add_equations_args_lessdef:
  forall rs ls rl tyl ll e e',
  add_equations_args rl tyl ll e = Some e' ->
  satisf rs ls e' ->
  Val.has_type_list (rs##rl) tyl ->
  Val.lessdef_list (rs##rl) (map (fun p => Locmap.getpair p ls) ll).
Proof.
  intros until e'. functional induction (add_equations_args rl tyl ll e); simpl; intros.
- inv H; auto.
- destruct H1. constructor; auto.
  eapply add_equation_lessdef with (q := Eq Full r1 l1). eapply add_equations_args_satisf; eauto.
- destruct H1. constructor; auto.
  rewrite <- (val_longofwords_eq (rs#r1)); auto. apply Val.longofwords_lessdef.
  eapply add_equation_lessdef with (q := Eq High r1 l1).
  eapply add_equation_satisf. eapply add_equations_args_satisf; eauto.
  eapply add_equation_lessdef with (q := Eq Low r1 l2).
  eapply add_equations_args_satisf; eauto.
- discriminate.
Qed.

Lemma add_equation_ros_satisf:
  forall rs ls ros mos e e',
  add_equation_ros ros mos e = Some e' ->
  satisf rs ls e' -> satisf rs ls e.
Proof.
  unfold add_equation_ros; intros. destruct ros; destruct mos; MonadInv.
  eapply add_equation_satisf; eauto.
  auto.
Qed.

Lemma remove_equation_satisf:
  forall rs ls q e,
  satisf rs ls e -> satisf rs ls (remove_equation q e).
Proof.
  intros. eapply satisf_incr; eauto. unfold remove_equation; simpl. ESD.fsetdec.
Qed.

Lemma remove_equation_res_satisf:
  forall rs ls r l e e',
  remove_equations_res r l e = Some e' ->
  satisf rs ls e -> satisf rs ls e'.
Proof.
  intros. functional inversion H.
  apply remove_equation_satisf; auto.
  apply remove_equation_satisf. apply remove_equation_satisf; auto.
Qed.

Remark select_reg_l_monotone:
  forall r q1 q2,
  OrderedEquation.eq q1 q2 \/ OrderedEquation.lt q1 q2 ->
  select_reg_l r q1 = true -> select_reg_l r q2 = true.
Proof.
  unfold select_reg_l; intros. destruct H.
  red in H. congruence.
  rewrite Pos.leb_le in *. red in H. destruct H as [A | [A B]].
  red in A. zify; omega.
  rewrite <- A; auto.
Qed.

Remark select_reg_h_monotone:
  forall r q1 q2,
  OrderedEquation.eq q1 q2 \/ OrderedEquation.lt q2 q1 ->
  select_reg_h r q1 = true -> select_reg_h r q2 = true.
Proof.
  unfold select_reg_h; intros. destruct H.
  red in H. congruence.
  rewrite Pos.leb_le in *. red in H. destruct H as [A | [A B]].
  red in A. zify; omega.
  rewrite A; auto.
Qed.

Remark select_reg_charact:
  forall r q, select_reg_l r q = true /\ select_reg_h r q = true <-> ereg q = r.
Proof.
  unfold select_reg_l, select_reg_h; intros; split.
  rewrite ! Pos.leb_le. unfold reg; zify; omega.
  intros. rewrite H. rewrite ! Pos.leb_refl; auto.
Qed.

Lemma reg_unconstrained_sound:
  forall r e q,
  reg_unconstrained r e = true ->
  EqSet.In q e ->
  ereg q <> r.
Proof.
  unfold reg_unconstrained; intros. red; intros.
  apply select_reg_charact in H1.
  assert (EqSet.mem_between (select_reg_l r) (select_reg_h r) e = true).
  {
    apply EqSet.mem_between_2 with q; auto.
    exact (select_reg_l_monotone r).
    exact (select_reg_h_monotone r).
    tauto.
    tauto.
  }
  rewrite H2 in H; discriminate.
Qed.

Lemma reg_unconstrained_satisf:
  forall r e rs ls v,
  reg_unconstrained r e = true ->
  satisf rs ls e ->
  satisf (rs#r <- v) ls e.
Proof.
  red; intros. rewrite PMap.gso. auto. eapply reg_unconstrained_sound; eauto.
Qed.

Remark select_loc_l_monotone:
  forall l q1 q2,
  OrderedEquation'.eq q1 q2 \/ OrderedEquation'.lt q1 q2 ->
  select_loc_l l q1 = true -> select_loc_l l q2 = true.
Proof.
  unfold select_loc_l; intros. set (lb := OrderedLoc.diff_low_bound l) in *.
  destruct H.
  red in H. subst q2; auto.
  assert (eloc q1 = eloc q2 \/ OrderedLoc.lt (eloc q1) (eloc q2)).
    red in H. tauto.
  destruct H1. rewrite <- H1; auto.
  destruct (OrderedLoc.compare (eloc q2) lb); auto.
  assert (OrderedLoc.lt (eloc q1) lb) by (eapply OrderedLoc.lt_trans; eauto).
  destruct (OrderedLoc.compare (eloc q1) lb).
  auto.
  eelim OrderedLoc.lt_not_eq; eauto.
  eelim OrderedLoc.lt_not_eq. eapply OrderedLoc.lt_trans. eexact l1. eexact H2. red; auto.
Qed.

Remark select_loc_h_monotone:
  forall l q1 q2,
  OrderedEquation'.eq q1 q2 \/ OrderedEquation'.lt q2 q1 ->
  select_loc_h l q1 = true -> select_loc_h l q2 = true.
Proof.
  unfold select_loc_h; intros. set (lb := OrderedLoc.diff_high_bound l) in *.
  destruct H.
  red in H. subst q2; auto.
  assert (eloc q2 = eloc q1 \/ OrderedLoc.lt (eloc q2) (eloc q1)).
    red in H. tauto.
  destruct H1. rewrite H1; auto.
  destruct (OrderedLoc.compare (eloc q2) lb); auto.
  assert (OrderedLoc.lt lb (eloc q1)) by (eapply OrderedLoc.lt_trans; eauto).
  destruct (OrderedLoc.compare (eloc q1) lb).
  eelim OrderedLoc.lt_not_eq. eapply OrderedLoc.lt_trans. eexact l1. eexact H2. red; auto.
  eelim OrderedLoc.lt_not_eq. eexact H2. apply OrderedLoc.eq_sym; auto.
  auto.
Qed.

Remark select_loc_charact:
  forall l q,
  select_loc_l l q = false \/ select_loc_h l q = false <-> Loc.diff l (eloc q).
Proof.
  unfold select_loc_l, select_loc_h; intros; split; intros.
  apply OrderedLoc.outside_interval_diff.
  destruct H.
  left. destruct (OrderedLoc.compare (eloc q) (OrderedLoc.diff_low_bound l)); assumption || discriminate.
  right. destruct (OrderedLoc.compare (eloc q) (OrderedLoc.diff_high_bound l)); assumption || discriminate.
  exploit OrderedLoc.diff_outside_interval. eauto.
  intros [A | A].
  left. destruct (OrderedLoc.compare (eloc q) (OrderedLoc.diff_low_bound l)).
  auto.
  eelim OrderedLoc.lt_not_eq; eauto.
  eelim OrderedLoc.lt_not_eq. eapply OrderedLoc.lt_trans; eauto. red; auto.
  right. destruct (OrderedLoc.compare (eloc q) (OrderedLoc.diff_high_bound l)).
  eelim OrderedLoc.lt_not_eq. eapply OrderedLoc.lt_trans; eauto. red; auto.
  eelim OrderedLoc.lt_not_eq; eauto. apply OrderedLoc.eq_sym; auto.
  auto.
Qed.

Lemma loc_unconstrained_sound:
  forall l e q,
  loc_unconstrained l e = true ->
  EqSet.In q e ->
  Loc.diff l (eloc q).
Proof.
  unfold loc_unconstrained; intros.
  destruct (select_loc_l l q) eqn:SL.
  destruct (select_loc_h l q) eqn:SH.
  assert (EqSet2.mem_between (select_loc_l l) (select_loc_h l) (eqs2 e) = true).
  {
    apply EqSet2.mem_between_2 with q; auto.
    exact (select_loc_l_monotone l).
    exact (select_loc_h_monotone l).
    apply eqs_same. auto.
  }
  rewrite H1 in H; discriminate.
  apply select_loc_charact; auto.
  apply select_loc_charact; auto.
Qed.

Lemma loc_unconstrained_satisf:
  forall rs ls k r mr e v,
  let l := R mr in
  satisf rs ls (remove_equation (Eq k r l) e) ->
  loc_unconstrained (R mr) (remove_equation (Eq k r l) e) = true ->
  Val.lessdef (sel_val k rs#r) v ->
  satisf rs (Locmap.set l v ls) e.
Proof.
  intros; red; intros.
  destruct (OrderedEquation.eq_dec q (Eq k r l)).
  subst q; simpl. unfold l; rewrite Locmap.gss. auto.
  assert (EqSet.In q (remove_equation (Eq k r l) e)).
    simpl. ESD.fsetdec.
  rewrite Locmap.gso. apply H; auto. eapply loc_unconstrained_sound; eauto.
Qed.

Lemma reg_loc_unconstrained_sound:
  forall r l e q,
  reg_loc_unconstrained r l e = true ->
  EqSet.In q e ->
  ereg q <> r /\ Loc.diff l (eloc q).
Proof.
  intros. destruct (andb_prop _ _ H).
  split. eapply reg_unconstrained_sound; eauto. eapply loc_unconstrained_sound; eauto.
Qed.

Lemma parallel_assignment_satisf:
  forall k r mr e rs ls v v',
  let l := R mr in
  Val.lessdef (sel_val k v) v' ->
  reg_loc_unconstrained r (R mr) (remove_equation (Eq k r l) e) = true ->
  satisf rs ls (remove_equation (Eq k r l) e) ->
  satisf (rs#r <- v) (Locmap.set l v' ls) e.
Proof.
  intros; red; intros.
  destruct (OrderedEquation.eq_dec q (Eq k r l)).
  subst q; simpl. unfold l; rewrite Regmap.gss; rewrite Locmap.gss; auto.
  assert (EqSet.In q (remove_equation {| ekind := k; ereg := r; eloc := l |} e)).
    simpl. ESD.fsetdec.
  exploit reg_loc_unconstrained_sound; eauto. intros [A B].
  rewrite Regmap.gso; auto. rewrite Locmap.gso; auto.
Qed.

Lemma parallel_assignment_satisf_2:
  forall rs ls res res' e e' v v',
  remove_equations_res res res' e = Some e' ->
  satisf rs ls e' ->
  reg_unconstrained res e' = true ->
  forallb (fun l => loc_unconstrained l e') (map R (regs_of_rpair res')) = true ->
  Val.lessdef v v' ->
  satisf (rs#res <- v) (Locmap.setpair res' v' ls) e.
Proof.
  intros. functional inversion H.
- (* One location *)
  subst. simpl in H2. InvBooleans. simpl. 
  apply parallel_assignment_satisf with Full; auto.
  unfold reg_loc_unconstrained. rewrite H1, H4. auto.
- (* Two 32-bit halves *)
  subst.
  set (e' := remove_equation {| ekind := Low; ereg := res; eloc := R mr2 |}
          (remove_equation {| ekind := High; ereg := res; eloc := R mr1 |} e)) in *.
  simpl in H2. InvBooleans. simpl.
  red; intros.
  destruct (OrderedEquation.eq_dec q (Eq Low res (R mr2))).
  subst q; simpl. rewrite Regmap.gss. rewrite Locmap.gss. 
  apply Val.loword_lessdef; auto.
  destruct (OrderedEquation.eq_dec q (Eq High res (R mr1))).
  subst q; simpl. rewrite Regmap.gss. rewrite Locmap.gso by auto. rewrite Locmap.gss. 
  apply Val.hiword_lessdef; auto.
  assert (EqSet.In q e'). unfold e', remove_equation; simpl; ESD.fsetdec.
  rewrite Regmap.gso. rewrite ! Locmap.gso. auto.
  eapply loc_unconstrained_sound; eauto.
  eapply loc_unconstrained_sound; eauto.
  eapply reg_unconstrained_sound; eauto.
Qed.

Lemma in_subst_reg:
  forall r1 r2 q (e: eqs),
  EqSet.In q e ->
  ereg q = r1 /\ EqSet.In (Eq (ekind q) r2 (eloc q)) (subst_reg r1 r2 e)
  \/ ereg q <> r1 /\ EqSet.In q (subst_reg r1 r2 e).
Proof.
  intros r1 r2 q e0 IN0. unfold subst_reg.
  set (f := fun (q: EqSet.elt) e => add_equation (Eq (ekind q) r2 (eloc q)) (remove_equation q e)).
  set (elt := EqSet.elements_between (select_reg_l r1) (select_reg_h r1) e0).
  assert (IN_ELT: forall q, EqSet.In q elt <-> EqSet.In q e0 /\ ereg q = r1).
  {
    intros. unfold elt. rewrite EqSet.elements_between_iff.
    rewrite select_reg_charact. tauto.
    exact (select_reg_l_monotone r1).
    exact (select_reg_h_monotone r1).
  }
  set (P := fun e1 e2 =>
         EqSet.In q e1 ->
         EqSet.In (Eq (ekind q) r2 (eloc q)) e2).
  assert (P elt (EqSet.fold f elt e0)).
  {
    apply ESP.fold_rec; unfold P; intros.
    - ESD.fsetdec.
    - simpl. red in H1. apply H1 in H3. destruct H3.
      + subst x. ESD.fsetdec.
      + rewrite ESF.add_iff. rewrite ESF.remove_iff.
        destruct (OrderedEquation.eq_dec x {| ekind := ekind q; ereg := r2; eloc := eloc q |}); auto.
        left. subst x; auto.
  }
  set (Q := fun e1 e2 =>
         ~EqSet.In q e1 ->
         EqSet.In q e2).
  assert (Q elt (EqSet.fold f elt e0)).
  {
    apply ESP.fold_rec; unfold Q; intros.
    - auto.
    - simpl. red in H2. rewrite H2 in H4.
      rewrite ESF.add_iff. rewrite ESF.remove_iff.
      right. split. apply H3. tauto. tauto.
  }
  destruct (ESP.In_dec q elt).
  left. split. apply IN_ELT. auto. apply H. auto.
  right. split. red; intros. elim n. rewrite IN_ELT. auto. apply H0. auto.
Qed.

Lemma subst_reg_satisf:
  forall src dst rs ls e,
  satisf rs ls (subst_reg dst src e) ->
  satisf (rs#dst <- (rs#src)) ls e.
Proof.
  intros; red; intros.
  destruct (in_subst_reg dst src q e H0) as [[A B] | [A B]].
  subst dst. rewrite Regmap.gss. exploit H; eauto.
  rewrite Regmap.gso; auto.
Qed.

Lemma in_subst_reg_kind:
  forall r1 k1 r2 k2 q (e: eqs),
  EqSet.In q e ->
  (ereg q, ekind q) = (r1, k1) /\ EqSet.In (Eq k2 r2 (eloc q)) (subst_reg_kind r1 k1 r2 k2 e)
  \/ EqSet.In q (subst_reg_kind r1 k1 r2 k2 e).
Proof.
  intros r1 k1 r2 k2 q e0 IN0. unfold subst_reg.
  set (f := fun (q: EqSet.elt) e =>
      if IndexedEqKind.eq (ekind q) k1
      then add_equation (Eq k2 r2 (eloc q)) (remove_equation q e)
      else e).
  set (elt := EqSet.elements_between (select_reg_l r1) (select_reg_h r1) e0).
  assert (IN_ELT: forall q, EqSet.In q elt <-> EqSet.In q e0 /\ ereg q = r1).
  {
    intros. unfold elt. rewrite EqSet.elements_between_iff.
    rewrite select_reg_charact. tauto.
    exact (select_reg_l_monotone r1).
    exact (select_reg_h_monotone r1).
  }
  set (P := fun e1 e2 =>
         EqSet.In q e1 -> ekind q = k1 ->
         EqSet.In (Eq k2 r2 (eloc q)) e2).
  assert (P elt (EqSet.fold f elt e0)).
  {
    intros; apply ESP.fold_rec; unfold P; intros.
    - ESD.fsetdec.
    - simpl. red in H1. apply H1 in H3. destruct H3.
      + subst x. unfold f. destruct (IndexedEqKind.eq (ekind q) k1).
        simpl. ESD.fsetdec. contradiction.
      + unfold f. destruct (IndexedEqKind.eq (ekind x) k1).
        simpl. rewrite ESF.add_iff. rewrite ESF.remove_iff.
        destruct (OrderedEquation.eq_dec x {| ekind := k2; ereg := r2; eloc := eloc q |}); auto.
        left. subst x; auto.
        auto.
  }
  set (Q := fun e1 e2 =>
         ~EqSet.In q e1 \/ ekind q <> k1 ->
         EqSet.In q e2).
  assert (Q elt (EqSet.fold f elt e0)).
  {
    apply ESP.fold_rec; unfold Q; intros.
    - auto.
    - unfold f. red in H2. rewrite H2 in H4.
      destruct (IndexedEqKind.eq (ekind x) k1).
      simpl. rewrite ESF.add_iff. rewrite ESF.remove_iff.
      right. split. apply H3. tauto. intuition congruence.
      apply H3. intuition.
  }
  destruct (ESP.In_dec q elt).
  destruct (IndexedEqKind.eq (ekind q) k1).
  left. split. f_equal. apply IN_ELT. auto. auto. apply H. auto. auto.
  right. apply H0. auto.
  right. apply H0. auto.
Qed.

Lemma subst_reg_kind_satisf_makelong:
  forall src1 src2 dst rs ls e,
  let e1 := subst_reg_kind dst High src1 Full e in
  let e2 := subst_reg_kind dst Low src2 Full e1 in
  reg_unconstrained dst e2 = true ->
  satisf rs ls e2 ->
  satisf (rs#dst <- (Val.longofwords rs#src1 rs#src2)) ls e.
Proof.
  intros; red; intros.
  destruct (in_subst_reg_kind dst High src1 Full q e H1) as [[A B] | B]; fold e1 in B.
  destruct (in_subst_reg_kind dst Low src2 Full _ e1 B) as [[C D] | D]; fold e2 in D.
  simpl in C; simpl in D. inv C.
  inversion A. rewrite H3; rewrite H4. rewrite Regmap.gss.
  apply Val.lessdef_trans with (rs#src1).
  simpl. destruct (rs#src1); simpl; auto. destruct (rs#src2); simpl; auto.
  rewrite Int64.hi_ofwords. auto.
  exploit H0. eexact D. simpl. auto.
  destruct (in_subst_reg_kind dst Low src2 Full q e1 B) as [[C D] | D]; fold e2 in D.
  inversion C. rewrite H3; rewrite H4. rewrite Regmap.gss.
  apply Val.lessdef_trans with (rs#src2).
  simpl. destruct (rs#src1); simpl; auto. destruct (rs#src2); simpl; auto.
  rewrite Int64.lo_ofwords. auto.
  exploit H0. eexact D. simpl. auto.
  rewrite Regmap.gso. apply H0; auto. eapply reg_unconstrained_sound; eauto.
Qed.

Lemma subst_reg_kind_satisf_lowlong:
  forall src dst rs ls e,
  let e1 := subst_reg_kind dst Full src Low e in
  reg_unconstrained dst e1 = true ->
  satisf rs ls e1 ->
  satisf (rs#dst <- (Val.loword rs#src)) ls e.
Proof.
  intros; red; intros.
  destruct (in_subst_reg_kind dst Full src Low q e H1) as [[A B] | B]; fold e1 in B.
  inversion A. rewrite H3; rewrite H4. simpl. rewrite Regmap.gss.
  exploit H0. eexact B. simpl. auto.
  rewrite Regmap.gso. apply H0; auto. eapply reg_unconstrained_sound; eauto.
Qed.

Lemma subst_reg_kind_satisf_highlong:
  forall src dst rs ls e,
  let e1 := subst_reg_kind dst Full src High e in
  reg_unconstrained dst e1 = true ->
  satisf rs ls e1 ->
  satisf (rs#dst <- (Val.hiword rs#src)) ls e.
Proof.
  intros; red; intros.
  destruct (in_subst_reg_kind dst Full src High q e H1) as [[A B] | B]; fold e1 in B.
  inversion A. rewrite H3; rewrite H4. simpl. rewrite Regmap.gss.
  exploit H0. eexact B. simpl. auto.
  rewrite Regmap.gso. apply H0; auto. eapply reg_unconstrained_sound; eauto.
Qed.

Module ESF2 := FSetFacts.Facts(EqSet2).
Module ESP2 := FSetProperties.Properties(EqSet2).
Module ESD2 := FSetDecide.Decide(EqSet2).

Lemma in_subst_loc:
  forall l1 l2 q (e e': eqs),
  EqSet.In q e ->
  subst_loc l1 l2 e = Some e' ->
  (eloc q = l1 /\ EqSet.In (Eq (ekind q) (ereg q) l2) e') \/ (Loc.diff l1 (eloc q) /\ EqSet.In q e').
Proof.
  intros l1 l2 q e0 e0'.
  unfold subst_loc.
  set (f := fun (q0 : EqSet2.elt) (opte : option eqs) =>
   match opte with
   | Some e =>
       if Loc.eq l1 (eloc q0)
       then
        Some
          (add_equation {| ekind := ekind q0; ereg := ereg q0; eloc := l2 |}
             (remove_equation q0 e))
       else None
   | None => None
   end).
  set (elt := EqSet2.elements_between (select_loc_l l1) (select_loc_h l1) (eqs2 e0)).
  intros IN SUBST.
  set (P := fun e1 (opte: option eqs) =>
          match opte with
          | None => True
          | Some e2 =>
              EqSet2.In q e1 ->
              eloc q = l1 /\ EqSet.In (Eq (ekind q) (ereg q) l2) e2
          end).
  assert (P elt (EqSet2.fold f elt (Some e0))).
  {
    apply ESP2.fold_rec; unfold P; intros.
    - ESD2.fsetdec.
    - destruct a as [e2|]; simpl; auto.
      destruct (Loc.eq l1 (eloc x)); auto.
      unfold add_equation, remove_equation; simpl.
      red in H1. rewrite H1. intros [A|A].
      + subst x. split. auto. ESD.fsetdec.
      + exploit H2; eauto. intros [B C]. split. auto.
        rewrite ESF.add_iff. rewrite ESF.remove_iff.
        destruct (OrderedEquation.eq_dec x {| ekind := ekind q; ereg := ereg q; eloc := l2 |}).
        left. rewrite e1; auto.
        right; auto.
  }
  set (Q := fun e1 (opte: option eqs) =>
          match opte with
          | None => True
          | Some e2 => ~EqSet2.In q e1 -> EqSet.In q e2
          end).
  assert (Q elt (EqSet2.fold f elt (Some e0))).
  {
    apply ESP2.fold_rec; unfold Q; intros.
    - auto.
    - destruct a as [e2|]; simpl; auto.
      destruct (Loc.eq l1 (eloc x)); auto.
      red in H2. rewrite H2; intros.
      unfold add_equation, remove_equation; simpl.
      rewrite ESF.add_iff. rewrite ESF.remove_iff.
      right; split. apply H3. tauto. tauto.
  }
  rewrite SUBST in H; rewrite SUBST in H0; simpl in *.
  destruct (ESP2.In_dec q elt).
  left. apply H; auto.
  right. split; auto.
  rewrite <- select_loc_charact.
  destruct (select_loc_l l1 q) eqn: LL; auto.
  destruct (select_loc_h l1 q) eqn: LH; auto.
  elim n. eapply EqSet2.elements_between_iff.
  exact (select_loc_l_monotone l1).
  exact (select_loc_h_monotone l1).
  split. apply eqs_same; auto. auto.
Qed.

Lemma loc_type_compat_charact:
  forall env l e q,
  loc_type_compat env l e = true ->
  EqSet.In q e ->
  subtype (sel_type (ekind q) (env (ereg q))) (Loc.type l) = true \/ Loc.diff l (eloc q).
Proof.
  unfold loc_type_compat; intros.
  rewrite EqSet2.for_all_between_iff in H.
  destruct (select_loc_l l q) eqn: LL.
  destruct (select_loc_h l q) eqn: LH.
  left; apply H; auto. apply eqs_same; auto.
  right. apply select_loc_charact. auto.
  right. apply select_loc_charact. auto.
  intros; subst; auto.
  exact (select_loc_l_monotone l).
  exact (select_loc_h_monotone l).
Qed.

Lemma well_typed_move_charact:
  forall env l e k r rs,
  well_typed_move env l e = true ->
  EqSet.In (Eq k r l) e ->
  wt_regset env rs ->
  match l with
  | R mr => True
  | S sl ofs ty => Val.has_type (sel_val k rs#r) ty
  end.
Proof.
  unfold well_typed_move; intros.
  destruct l as [mr | sl ofs ty].
  auto.
  exploit loc_type_compat_charact; eauto. intros [A | A].
  simpl in A. eapply Val.has_subtype; eauto.
  generalize (H1 r). destruct k; simpl; intros.
  auto.
  destruct (rs#r); exact I.
  destruct (rs#r); exact I.
  eelim Loc.diff_not_eq. eexact A. auto.
Qed.

Remark val_lessdef_normalize:
  forall v v' ty,
  Val.has_type v ty -> Val.lessdef v v' ->
  Val.lessdef v (Val.load_result (chunk_of_type ty) v').
Proof.
  intros. inv H0. rewrite Val.load_result_same; auto. auto.
Qed.

Lemma subst_loc_satisf:
  forall env src dst rs ls e e',
  subst_loc dst src e = Some e' ->
  well_typed_move env dst e = true ->
  wt_regset env rs ->
  satisf rs ls e' ->
  satisf rs (Locmap.set dst (ls src) ls) e.
Proof.
  intros; red; intros.
  exploit in_subst_loc; eauto. intros [[A B] | [A B]].
  subst dst. rewrite Locmap.gss.
  destruct q as [k r l]; simpl in *.
  exploit well_typed_move_charact; eauto.
  destruct l as [mr | sl ofs ty]; intros.
  apply (H2 _ B).
  apply val_lessdef_normalize; auto. apply (H2 _ B).
  rewrite Locmap.gso; auto.
Qed.

Lemma can_undef_sound:
  forall e ml q,
  can_undef ml e = true -> EqSet.In q e -> Loc.notin (eloc q) (map R ml).
Proof.
  induction ml; simpl; intros.
  tauto.
  InvBooleans. split.
  apply Loc.diff_sym. eapply loc_unconstrained_sound; eauto.
  eauto.
Qed.

Lemma undef_regs_outside:
  forall ml ls l,
  Loc.notin l (map R ml) -> undef_regs ml ls l = ls l.
Proof.
  induction ml; simpl; intros. auto.
  rewrite Locmap.gso. apply IHml. tauto. apply Loc.diff_sym. tauto.
Qed.

Lemma can_undef_satisf:
  forall ml e rs ls,
  can_undef ml e = true ->
  satisf rs ls e ->
  satisf rs (undef_regs ml ls) e.
Proof.
  intros; red; intros. rewrite undef_regs_outside. eauto.
  eapply can_undef_sound; eauto.
Qed.

Lemma can_undef_except_sound:
  forall lx e ml q,
  can_undef_except lx ml e = true -> EqSet.In q e -> Loc.diff (eloc q) lx -> Loc.notin (eloc q) (map R ml).
Proof.
  induction ml; simpl; intros.
  tauto.
  InvBooleans. split.
  destruct (orb_true_elim _ _ H2).
  apply proj_sumbool_true in e0. congruence.
  apply Loc.diff_sym. eapply loc_unconstrained_sound; eauto.
  eapply IHml; eauto.
Qed.

Lemma subst_loc_undef_satisf:
  forall env src dst rs ls ml e e',
  subst_loc dst src e = Some e' ->
  well_typed_move env dst e = true ->
  can_undef_except dst ml e = true ->
  wt_regset env rs ->
  satisf rs ls e' ->
  satisf rs (Locmap.set dst (ls src) (undef_regs ml ls)) e.
Proof.
  intros; red; intros.
  exploit in_subst_loc; eauto. intros [[A B] | [A B]].
  subst dst. rewrite Locmap.gss.
  destruct q as [k r l]; simpl in *.
  exploit well_typed_move_charact; eauto.
  destruct l as [mr | sl ofs ty]; intros.
  apply (H3 _ B).
  apply val_lessdef_normalize; auto. apply (H3 _ B).
  rewrite Locmap.gso; auto. rewrite undef_regs_outside. eauto.
  eapply can_undef_except_sound; eauto. apply Loc.diff_sym; auto.
Qed.

Lemma transfer_use_def_satisf:
  forall args res args' res' und e e' rs ls,
  transfer_use_def args res args' res' und e = Some e' ->
  satisf rs ls e' ->
  Val.lessdef_list rs##args (reglist ls args') /\
  (forall v v', Val.lessdef v v' ->
    satisf (rs#res <- v) (Locmap.set (R res') v' (undef_regs und ls)) e).
Proof.
  unfold transfer_use_def; intros. MonadInv.
  split. eapply add_equations_lessdef; eauto.
  intros. eapply parallel_assignment_satisf; eauto. assumption.
  eapply can_undef_satisf; eauto.
  eapply add_equations_satisf; eauto.
Qed.

Lemma add_equations_res_lessdef:
  forall r oty l e e' rs ls,
  add_equations_res r oty l e = Some e' ->
  satisf rs ls e' ->
  Val.has_type rs#r (match oty with Some ty => ty | None => Tint end) ->
  Val.lessdef rs#r (Locmap.getpair (map_rpair R l) ls).
Proof.
  intros. functional inversion H; simpl.
- subst. eapply add_equation_lessdef with (q := Eq Full r (R mr)); eauto.
- subst. rewrite <- (val_longofwords_eq rs#r) by auto. 
  apply Val.longofwords_lessdef.
  eapply add_equation_lessdef with (q := Eq High r (R mr1)).
  eapply add_equation_satisf. eauto.
  eapply add_equation_lessdef with (q := Eq Low r (R mr2)).
  eauto.
Qed.

Definition callee_save_loc (l: loc) :=
  match l with
  | R r => is_callee_save r = true
  | S sl ofs ty => sl <> Outgoing
  end.

Definition agree_callee_save (ls1 ls2: locset) : Prop :=
  forall l, callee_save_loc l -> ls1 l = ls2 l.

Lemma return_regs_agree_callee_save:
  forall caller callee,
  agree_callee_save caller (return_regs caller callee).
Proof.
  intros; red; intros. unfold return_regs. red in H.
  destruct l.
  rewrite H; auto. 
  destruct sl; auto || congruence.
Qed.

Lemma no_caller_saves_sound:
  forall e q,
  no_caller_saves e = true ->
  EqSet.In q e ->
  callee_save_loc (eloc q).
Proof.
  unfold no_caller_saves, callee_save_loc; intros.
  exploit EqSet.for_all_2; eauto.
  hnf. intros. simpl in H1. rewrite H1. auto.
  lazy beta. destruct (eloc q). auto. destruct sl; congruence.
Qed.

Lemma val_hiword_longofwords:
  forall v1 v2, Val.lessdef (Val.hiword (Val.longofwords v1 v2)) v1.
Proof.
  intros. destruct v1; simpl; auto. destruct v2; auto. unfold Val.hiword.
  rewrite Int64.hi_ofwords. auto.
Qed.

Lemma val_loword_longofwords:
  forall v1 v2, Val.lessdef (Val.loword (Val.longofwords v1 v2)) v2.
Proof.
  intros. destruct v1; simpl; auto. destruct v2; auto. unfold Val.loword.
  rewrite Int64.lo_ofwords. auto.
Qed.

Lemma function_return_satisf:
  forall rs ls_before ls_after res res' sg e e' v,
  res' = loc_result sg ->
  remove_equations_res res res' e = Some e' ->
  satisf rs ls_before e' ->
  forallb (fun l => reg_loc_unconstrained res l e') (map R (regs_of_rpair res')) = true ->
  no_caller_saves e' = true ->
  Val.lessdef v (Locmap.getpair (map_rpair R res') ls_after) ->
  agree_callee_save ls_before ls_after ->
  satisf (rs#res <- v) ls_after e.
Proof.
  intros; red; intros.
  functional inversion H0.
- (* One register *)
  subst. rewrite <- H8 in *. simpl in *. InvBooleans.
  set (e' := remove_equation {| ekind := Full; ereg := res; eloc := R mr |} e) in *.
  destruct (OrderedEquation.eq_dec q (Eq Full res (R mr))).
  subst q; simpl. rewrite Regmap.gss; auto.
  assert (EqSet.In q e'). unfold e', remove_equation; simpl. ESD.fsetdec.
  exploit reg_loc_unconstrained_sound; eauto. intros [A B].
  rewrite Regmap.gso; auto.
  exploit no_caller_saves_sound; eauto. intros.
  red in H5. rewrite <- H5; auto.
- (* Two 32-bit halves *)
  subst. rewrite <- H9 in *. simpl in *. 
  set (e' := remove_equation {| ekind := Low; ereg := res; eloc := R mr2 |}
          (remove_equation {| ekind := High; ereg := res; eloc := R mr1 |} e)) in *.
  InvBooleans.
  destruct (OrderedEquation.eq_dec q (Eq Low res (R mr2))).
  subst q; simpl. rewrite Regmap.gss.
  eapply Val.lessdef_trans. apply Val.loword_lessdef. eauto. apply val_loword_longofwords.
  destruct (OrderedEquation.eq_dec q (Eq High res (R mr1))).
  subst q; simpl. rewrite Regmap.gss.
  eapply Val.lessdef_trans. apply Val.hiword_lessdef. eauto. apply val_hiword_longofwords.
  assert (EqSet.In q e'). unfold e', remove_equation; simpl; ESD.fsetdec.
  exploit reg_loc_unconstrained_sound. eexact H. eauto. intros [A B].
  exploit reg_loc_unconstrained_sound. eexact H2. eauto. intros [C D].
  rewrite Regmap.gso; auto.
  exploit no_caller_saves_sound; eauto. intros.
  red in H5. rewrite <- H5; auto.
Qed.

Lemma compat_left_sound:
  forall r l e q,
  compat_left r l e = true -> EqSet.In q e -> ereg q = r -> ekind q = Full /\ eloc q = l.
Proof.
  unfold compat_left; intros.
  rewrite EqSet.for_all_between_iff in H.
  apply select_reg_charact in H1. destruct H1.
  exploit H; eauto. intros.
  destruct (ekind q); try discriminate.
  destruct (Loc.eq l (eloc q)); try discriminate.
  auto.
  intros. subst x2. auto.
  exact (select_reg_l_monotone r).
  exact (select_reg_h_monotone r).
Qed.

Lemma compat_left2_sound:
  forall r l1 l2 e q,
  compat_left2 r l1 l2 e = true -> EqSet.In q e -> ereg q = r ->
  (ekind q = High /\ eloc q = l1) \/ (ekind q = Low /\ eloc q = l2).
Proof.
  unfold compat_left2; intros.
  rewrite EqSet.for_all_between_iff in H.
  apply select_reg_charact in H1. destruct H1.
  exploit H; eauto. intros.
  destruct (ekind q); try discriminate.
  InvBooleans. auto.
  InvBooleans. auto.
  intros. subst x2. auto.
  exact (select_reg_l_monotone r).
  exact (select_reg_h_monotone r).
Qed.

Lemma compat_entry_satisf:
  forall rl ll e,
  compat_entry rl ll e = true ->
  forall vl ls,
  Val.lessdef_list vl (map (fun p => Locmap.getpair p ls) ll) ->
  satisf (init_regs vl rl) ls e.
Proof.
  intros until e. functional induction (compat_entry rl ll e); intros.
- (* no params *)
  simpl. red; intros. rewrite Regmap.gi. destruct (ekind q); simpl; auto.
- (* a param in a single location *)
  InvBooleans. simpl in H0. inv H0. simpl.
  red; intros. rewrite Regmap.gsspec. destruct (peq (ereg q) r1).
  exploit compat_left_sound; eauto. intros [A B]. rewrite A; rewrite B; auto.
  eapply IHb; eauto.
- (* a param split across two locations *)
  InvBooleans. simpl in H0. inv H0. simpl.
  red; intros. rewrite Regmap.gsspec. destruct (peq (ereg q) r1).
  exploit compat_left2_sound; eauto.
  intros [[A B] | [A B]]; rewrite A; rewrite B; simpl.
  apply Val.lessdef_trans with (Val.hiword (Val.longofwords (ls l1) (ls l2))).
  apply Val.hiword_lessdef; auto. apply val_hiword_longofwords.
  apply Val.lessdef_trans with (Val.loword (Val.longofwords (ls l1) (ls l2))).
  apply Val.loword_lessdef; auto. apply val_loword_longofwords.
  eapply IHb; eauto.
- (* error case *)
  discriminate.
Qed.

Lemma call_regs_param_values:
  forall sg ls,
  map (fun p => Locmap.getpair p (call_regs ls)) (loc_parameters sg)
  = map (fun p => Locmap.getpair p ls) (loc_arguments sg).
Proof.
  intros. unfold loc_parameters. rewrite list_map_compose.
  apply list_map_exten; intros. symmetry.
  assert (A: forall l, loc_argument_acceptable l -> call_regs ls (parameter_of_argument l) = ls l).
  { destruct l as [r | [] ofs ty]; simpl; auto; contradiction. }
  exploit loc_arguments_acceptable; eauto. destruct x; simpl; intros.
- auto.
- destruct H0; f_equal; auto.
Qed.

Lemma return_regs_arg_values:
  forall sg ls1 ls2,
  tailcall_is_possible sg = true ->
  map (fun p => Locmap.getpair p (return_regs ls1 ls2)) (loc_arguments sg) 
  = map (fun p => Locmap.getpair p ls2) (loc_arguments sg).
Proof.
  intros.
  apply tailcall_is_possible_correct in H.
  apply list_map_exten; intros.
  apply Locmap.getpair_exten; intros.
  assert (In l (regs_of_rpairs (loc_arguments sg))) by (eapply in_regs_of_rpairs; eauto).
  exploit loc_arguments_acceptable_2; eauto. exploit H; eauto. 
  destruct l; simpl; intros; try contradiction. rewrite H4; auto.
Qed.

Lemma find_function_tailcall:
  forall tge ros ls1 ls2,
  ros_compatible_tailcall ros = true ->
  find_function tge ros (return_regs ls1 ls2) = find_function tge ros ls2.
Proof.
  unfold ros_compatible_tailcall, find_function; intros.
  destruct ros as [r|id]; auto.
  unfold return_regs. destruct (is_callee_save r). discriminate. auto.
Qed.

Lemma loadv_int64_split:
  forall m a v,
  Mem.loadv Mint64 m a = Some v ->
  exists v1 v2,
     Mem.loadv Mint32 m a = Some (if Archi.big_endian then v1 else v2)
  /\ Mem.loadv  Mint32 m (Val.add a (Vint (Int.repr 4))) = Some (if Archi.big_endian then v2 else v1)
  /\ Val.lessdef (Val.hiword v) v1
  /\ Val.lessdef (Val.loword v) v2.
Proof.
  intros. exploit Mem.loadv_int64_split; eauto. intros (v1 & v2 & A & B & C).
  exists v1, v2. split; auto. split; auto.
  inv C; auto. destruct v1, v2; simpl; auto.
  rewrite Int64.hi_ofwords, Int64.lo_ofwords; auto.
Qed.

Lemma add_equations_builtin_arg_satisf:
  forall env rs ls arg arg' e e',
  add_equations_builtin_arg env arg arg' e = Some e' ->
  satisf rs ls e' -> satisf rs ls e.
Proof.
  induction arg; destruct arg'; simpl; intros; MonadInv; eauto.
  eapply add_equation_satisf; eauto.
  destruct arg'1; MonadInv. destruct arg'2; MonadInv. eauto using add_equation_satisf.
Qed.

Lemma add_equations_builtin_arg_lessdef:
  forall env (ge: RTL_memsem.genv) sp rs ls m arg v,
  eval_builtin_arg ge (fun r => rs#r) sp m arg v ->
  forall e e' arg',
  add_equations_builtin_arg env arg arg' e = Some e' ->
  satisf rs ls e' ->
  wt_regset env rs ->
  exists v', eval_builtin_arg ge ls sp m arg' v' /\ Val.lessdef v v'.
Proof.
  induction 1; simpl; intros e e' arg' AE SAT WT; destruct arg'; MonadInv.
- exploit add_equation_lessdef; eauto. simpl; intros.
  exists (ls x0); auto with barg.
- destruct arg'1; MonadInv. destruct arg'2; MonadInv.
  exploit add_equation_lessdef. eauto. simpl; intros LD1.
  exploit add_equation_lessdef. eapply add_equation_satisf. eauto. simpl; intros LD2.
  exists (Val.longofwords (ls x0) (ls x1)); split; auto with barg.
  rewrite <- (val_longofwords_eq rs#x). apply Val.longofwords_lessdef; auto.
  rewrite <- e0; apply WT.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- exploit IHeval_builtin_arg1; eauto. eapply add_equations_builtin_arg_satisf; eauto.
  intros (v1 & A & B).
  exploit IHeval_builtin_arg2; eauto. intros (v2 & C & D).
  exists (Val.longofwords v1 v2); split; auto with barg. apply Val.longofwords_lessdef; auto.
Qed.

Lemma add_equations_builtin_args_satisf:
  forall env rs ls arg arg' e e',
  add_equations_builtin_args env arg arg' e = Some e' ->
  satisf rs ls e' -> satisf rs ls e.
Proof.
  induction arg; destruct arg'; simpl; intros; MonadInv; eauto using add_equations_builtin_arg_satisf.
Qed.

Lemma add_equations_builtin_args_lessdef:
  forall env (ge: RTL_memsem.genv) sp rs ls m tm arg vl,
  eval_builtin_args ge (fun r => rs#r) sp m arg vl ->
  forall arg' e e',
  add_equations_builtin_args env arg arg' e = Some e' ->
  satisf rs ls e' ->
  wt_regset env rs ->
  Mem.extends m tm ->
  exists vl', eval_builtin_args ge ls sp tm arg' vl' /\ Val.lessdef_list vl vl'.
Proof.
  induction 1; simpl; intros; destruct arg'; MonadInv.
- exists (@nil val); split; constructor.
- exploit IHlist_forall2; eauto. intros (vl' & A & B).
  exploit add_equations_builtin_arg_lessdef; eauto.
  eapply add_equations_builtin_args_satisf; eauto. intros (v1' & C & D).
  exploit (@eval_builtin_arg_lessdef _ ge ls ls); eauto. intros (v1'' & E & F).
  exists (v1'' :: vl'); split; constructor; auto. eapply Val.lessdef_trans; eauto.
Qed.

Lemma add_equations_debug_args_satisf:
  forall env rs ls arg arg' e e',
  add_equations_debug_args env arg arg' e = Some e' ->
  satisf rs ls e' -> satisf rs ls e.
Proof.
  induction arg; destruct arg'; simpl; intros; MonadInv; auto.
  destruct (add_equations_builtin_arg env a b e) as [e1|] eqn:A;
  eauto using add_equations_builtin_arg_satisf.
Qed.

Lemma add_equations_debug_args_eval:
  forall env (ge: RTL_memsem.genv) sp rs ls m tm arg vl,
  eval_builtin_args ge (fun r => rs#r) sp m arg vl ->
  forall arg' e e',
  add_equations_debug_args env arg arg' e = Some e' ->
  satisf rs ls e' ->
  wt_regset env rs ->
  Mem.extends m tm ->
  exists vl', eval_builtin_args ge ls sp tm arg' vl'.
Proof.
  induction 1; simpl; intros; destruct arg'; MonadInv.
- exists (@nil val); constructor.
- exists (@nil val); constructor.
- destruct (add_equations_builtin_arg env a1 b e) as [e1|] eqn:A.
+ exploit IHlist_forall2; eauto. intros (vl' & B).
  exploit add_equations_builtin_arg_lessdef; eauto.
  eapply add_equations_debug_args_satisf; eauto. intros (v1' & C & D).
  exploit (@eval_builtin_arg_lessdef _ ge ls ls); eauto. intros (v1'' & E & F).
  exists (v1'' :: vl'); constructor; auto.
+ eauto.
Qed.
Lemma add_equations_debug_args_eval_LD:
  forall env (ge: RTL_memsem.genv) sp rs ls m tm arg vl,
  eval_builtin_args ge (fun r => rs#r) sp m arg vl ->
  forall arg' e e',
  add_equations_debug_args env arg arg' e = Some e' ->
  satisf rs ls e' ->
  wt_regset env rs ->
  Mem.extends m tm ->
  exists vl', eval_builtin_args ge ls sp tm arg' vl' /\
  forall v', In v' vl' -> exists v, In v vl /\ Val.lessdef v v'.
Proof.
  induction 1; simpl; intros; destruct arg'; MonadInv.
- exists (@nil val); split. constructor. contradiction.
- exists (@nil val); split. constructor. contradiction.
- destruct (add_equations_builtin_arg env a1 b e) as [e1|] eqn:A.
+ exploit IHlist_forall2; eauto. intros (vl' & B & X).
  exploit add_equations_builtin_arg_lessdef; eauto.
  eapply add_equations_debug_args_satisf; eauto. intros (v1' & C & D).
  exploit (@eval_builtin_arg_lessdef _ ge ls ls); eauto. intros (v1'' & E & F).
  exists (v1'' :: vl'); split. constructor; auto.
  intros. destruct H5. subst. exists b1; split. left; trivial. eapply Val.lessdef_trans; eassumption.
  destruct (X _ H5) as [x [HH1 HH2]]. exists x; split; trivial. right; trivial. 
+ destruct (IHlist_forall2 _ _ _ H1 H2 H3 H4) as [vl' [AA BB]].
  exists vl'; split. apply AA.
  intros. destruct (BB _ H5) as [x [CC DD]]. exists x; split; trivial. right; trivial.
Qed.

Lemma lessdef_list_lessdef_pointwise: forall vargs vargs', Val.lessdef_list vargs vargs' ->
      forall v', In v' vargs' -> exists v, In v vargs /\ Val.lessdef v v'.
Proof. induction 1; simpl; intros. contradiction.
  destruct H1; subst. exists v1; split; trivial. left; trivial.
  destruct (IHlessdef_list _ H1) as [x [A B]]. exists x; split; trivial. right; trivial.
Qed.
(*
Lemma add_equations_builtin_eval_LD:
  forall ef env args args' e1 e2 m1 m1' rs ls (ge: RTL_memsem.genv) sp vargs t vres m2,
  wt_regset env rs ->
  match ef with
  | EF_debug _ _ _ => add_equations_debug_args env args args' e1
  | _              => add_equations_builtin_args env args args' e1
  end = Some e2 ->
  Mem.extends m1 m1' ->
  satisf rs ls e2 ->
  eval_builtin_args ge (fun r => rs # r) sp m1 args vargs ->
  external_call ef ge vargs m1 t vres m2 ->
  satisf rs ls e1 /\
  exists vargs' vres' m2',
     eval_builtin_args ge ls sp m1' args' vargs'
  /\ external_call ef ge vargs' m1' t vres' m2'
  /\ Val.lessdef vres vres'
  /\ Mem.extends m2 m2' 
  /\ forall v', In v' vargs' -> exists v, In v vargs /\ Val.lessdef v v'.
Proof.
  intros.
  assert (DEFAULT: add_equations_builtin_args env args args' e1 = Some e2 ->
    satisf rs ls e1 /\
    exists vargs' vres' m2',
       eval_builtin_args ge ls sp m1' args' vargs'
    /\ external_call ef ge vargs' m1' t vres' m2'
    /\ Val.lessdef vres vres'
    /\ Mem.extends m2 m2'
    /\ forall v', In v' vargs' -> exists v, In v vargs /\ Val.lessdef v v').
  {
    intros. split. eapply add_equations_builtin_args_satisf; eauto.
    exploit add_equations_builtin_args_lessdef; eauto.
    intros (vargs' & A & B).
    exploit external_call_mem_extends; eauto.
    intros (vres' & m2' & C & D & E & F).
    specialize (lessdef_list_lessdef_pointwise _ _ B). intros BB.
    exists vargs', vres', m2'; auto.
  }
  destruct ef; auto.
  split. { eapply add_equations_debug_args_satisf; eauto. }
  exploit add_equations_debug_args_eval; eauto.
  intros (vargs' & A).
  simpl in H4; inv H4.
  exists vargs', Vundef, m1'. intuition auto. simpl. constructor. clear DEFAULT. 
  generalize dependent e2.
  generalize dependent e1.
  generalize dependent vargs'.
  generalize dependent vargs.
  generalize dependent args'.
  induction args; simpl; intros.
  + destruct args'; inv H0. inv H3. inv A. contradiction.
  + inv H3. 
    destruct args'.
    - inv H0. inv A. contradiction.
    - inv A. remember (add_equations_builtin_arg env a b e1). destruct o; symmetry in Heqo.
      * specialize (IHargs _ _ H9 _ H10).
        destruct H4; subst. 
        ++ clear IHargs H9 H10. exists b1; split. left; trivial.
           exploit add_equations_builtin_arg_lessdef. eassumption. eassumption. 2: eassumption.
             eapply add_equations_debug_args_satisf. eassumption. eassumption.
           intros [v [EV LD]]. eapply Val.lessdef_trans. eassumption. clear H7.
           exploit eval_builtin_arg_lessdef. 2: eassumption. 2: eassumption. intros. apply Val.lessdef_refl.
           intros [vv [EVV LDVV]]. 
           exploit eval_builtin_arg_determ. apply H6. apply EVV. intros; subst; trivial.
        ++ destruct (IHargs H3 _ _ H0 H2) as [ x [AA BB]]. exists x; split; trivial. right; trivial.
      * destruct H4; subst.
        ++ clear IHargs H9 H10.
           destruct a; destruct b; try discriminate.
           simpl in *. inv H7. inv H6. destruct args; simpl in H0. discriminate.  unfold eval_builtin_arg in H7. inv H6; inv H7.
           red in H. red in H2.
 exists b1; split. left; trivial.
           exploit add_equations_builtin_arg_lessdef. eassumption. eassumption. 2: eassumption.
             eapply add_equations_debug_args_satisf. eassumption. eassumption.
           intros [v [EV LD]]. eapply Val.lessdef_trans. eassumption. clear H7.
           exploit eval_builtin_arg_lessdef. 2: eassumption. 2: eassumption. intros. apply Val.lessdef_refl.
           intros [vv [EVV LDVV]]. 
           exploit eval_builtin_arg_determ. apply H6. apply EVV. intros; subst; trivial.
        ++ destruct (IHargs H3 _ _ H0 H2) as [ x [AA BB]]. exists x; split; trivial. right; trivial.
      * des destruct args; simpl in *. discriminate.
           remember (add_equations_builtin_arg env b0 b e1). destruct o. inv H9. unfold add_equations_debug_args in H0. inv H0. exists b1; split. left; trivial. 
           clear IHargs H9 H10. (* exists b1; split. left; trivial.*)
           destruct a; destruct b; simpl in *; try discriminate. inv H7. inv H6. inv H0.
           exploit add_equations_builtin_arg_lessdef. eassumption. eassumption. 2: eassumption.
             eapply add_equations_debug_args_satisf. eassumption. eassumption.
           intros [v [EV LD]]. eapply Val.lessdef_trans. eassumption. clear H7.
           exploit eval_builtin_arg_lessdef. 2: eassumption. 2: eassumption. intros. apply Val.lessdef_refl.
           intros [vv [EVV LDVV]]. 
           exploit eval_builtin_arg_determ. apply H6. apply EVV. intros; subst; trivial.
        ++ destruct (IHargs H3 _ _ H0 H2) as [ x [AA BB]]. exists x; split; trivial. right; trivial.
      *
  exploit (eval_builtin_args_lessdef). 2: eassumption. 2: eassumption.
  Focus 2. intros [vl [EB LD]].  eval_builtin_args_lessdef
  destruct (DEFAULT  intuition.
Qed.
*)

Lemma add_equations_builtin_eval:
  forall ef env args args' e1 e2 m1 m1' rs ls (ge: RTL_memsem.genv) sp vargs t vres m2,
  wt_regset env rs ->
  match ef with
  | EF_debug _ _ _ => add_equations_debug_args env args args' e1
  | _              => add_equations_builtin_args env args args' e1
  end = Some e2 ->
  Mem.extends m1 m1' ->
  satisf rs ls e2 ->
  eval_builtin_args ge (fun r => rs # r) sp m1 args vargs ->
  external_call ef ge vargs m1 t vres m2 ->
  satisf rs ls e1 /\
  exists vargs' vres' m2',
     eval_builtin_args ge ls sp m1' args' vargs'
  /\ external_call ef ge vargs' m1' t vres' m2'
  /\ Val.lessdef vres vres'
  /\ Mem.extends m2 m2'.
Proof.
  intros.
  assert (DEFAULT: add_equations_builtin_args env args args' e1 = Some e2 ->
    satisf rs ls e1 /\
    exists vargs' vres' m2',
       eval_builtin_args ge ls sp m1' args' vargs'
    /\ external_call ef ge vargs' m1' t vres' m2'
    /\ Val.lessdef vres vres'
    /\ Mem.extends m2 m2').
  {
    intros. split. eapply add_equations_builtin_args_satisf; eauto.
    exploit add_equations_builtin_args_lessdef; eauto.
    intros (vargs' & A & B).
    exploit external_call_mem_extends; eauto.
    intros (vres' & m2' & C & D & E & F).
    exists vargs', vres', m2'; auto.
  }
  destruct ef; auto.
  split. eapply add_equations_debug_args_satisf; eauto.
  exploit add_equations_debug_args_eval; eauto.
  intros (vargs' & A).
  simpl in H4; inv H4.
  exists vargs', Vundef, m1'. intuition auto. simpl. constructor.
Qed.

Lemma parallel_set_builtin_res_satisf:
  forall env res res' e0 e1 rs ls v v',
  remove_equations_builtin_res env res res' e0 = Some e1 ->
  forallb (fun r => reg_unconstrained r e1) (params_of_builtin_res res) = true ->
  forallb (fun mr => loc_unconstrained (R mr) e1) (params_of_builtin_res res') = true ->
  satisf rs ls e1 ->
  Val.lessdef v v' ->
  satisf (regmap_setres res v rs) (Locmap.setres res' v' ls) e0.
Proof.
  intros. rewrite forallb_forall in *.
  destruct res, res'; simpl in *; inv H.
- apply parallel_assignment_satisf with (k := Full); auto.
  unfold reg_loc_unconstrained. rewrite H0 by auto. rewrite H1 by auto. auto.
- destruct res'1; try discriminate. destruct res'2; try discriminate.
  rename x0 into hi; rename x1 into lo. MonadInv. destruct (mreg_eq hi lo); inv H5.
  set (e' := remove_equation {| ekind := High; ereg := x; eloc := R hi |} e0) in *.
  set (e'' := remove_equation {| ekind := Low; ereg := x; eloc := R lo |} e') in *.
  simpl in *. red; intros.
  destruct (OrderedEquation.eq_dec q (Eq Low x (R lo))).
  subst q; simpl. rewrite Regmap.gss. rewrite Locmap.gss. apply Val.loword_lessdef; auto.
  destruct (OrderedEquation.eq_dec q (Eq High x (R hi))).
  subst q; simpl. rewrite Regmap.gss. rewrite Locmap.gso by (red; auto).
  rewrite Locmap.gss. apply Val.hiword_lessdef; auto.
  assert (EqSet.In q e'').
  { unfold e'', e', remove_equation; simpl; ESD.fsetdec. }
  rewrite Regmap.gso. rewrite ! Locmap.gso. auto.
  eapply loc_unconstrained_sound; eauto.
  eapply loc_unconstrained_sound; eauto.
  eapply reg_unconstrained_sound; eauto.
- auto.
Qed.

(** * Properties of the dataflow analysis *)

Lemma analyze_successors:
  forall f env bsh an pc bs s e,
  analyze f env bsh = Some an ->
  bsh!pc = Some bs ->
  In s (successors_block_shape bs) ->
  an!!pc = OK e ->
  exists e', transfer f env bsh s an!!s = OK e' /\ EqSet.Subset e' e.
Proof.
  unfold analyze; intros. exploit DS.fixpoint_allnodes_solution; eauto.
  rewrite H2. unfold DS.L.ge. destruct (transfer f env bsh s an#s); intros.
  exists e0; auto.
  contradiction.
Qed.

Lemma satisf_successors:
  forall f env bsh an pc bs s e rs ls,
  analyze f env bsh = Some an ->
  bsh!pc = Some bs ->
  In s (successors_block_shape bs) ->
  an!!pc = OK e ->
  satisf rs ls e ->
  exists e', transfer f env bsh s an!!s = OK e' /\ satisf rs ls e'.
Proof.
  intros. exploit analyze_successors; eauto. intros [e' [A B]].
  exists e'; split; auto. eapply satisf_incr; eauto.
Qed.

(** Inversion on [transf_function] *)

Inductive transf_function_spec (f: RTL_memsem.function) (tf: LTL_memsem.function) : Prop :=
  | transf_function_spec_intro:
      forall env an mv k e1 e2,
      wt_function f env ->
      analyze f env (pair_codes f tf) = Some an ->
      (LTL_memsem.fn_code tf)!(LTL_memsem.fn_entrypoint tf) = Some(expand_moves mv (Lbranch (RTL_memsem.fn_entrypoint f) :: k)) ->
      wf_moves mv ->
      transfer f env (pair_codes f tf) (RTL_memsem.fn_entrypoint f) an!!(RTL_memsem.fn_entrypoint f) = OK e1 ->
      track_moves env mv e1 = Some e2 ->
      compat_entry (RTL_memsem.fn_params f) (loc_parameters (fn_sig tf)) e2 = true ->
      can_undef destroyed_at_function_entry e2 = true ->
      RTL_memsem.fn_stacksize f = LTL_memsem.fn_stacksize tf ->
      RTL_memsem.fn_sig f = LTL_memsem.fn_sig tf ->
      transf_function_spec f tf.

Lemma transf_function_inv:
  forall f tf,
  transf_function f = OK tf ->
  transf_function_spec f tf.
Proof.
  unfold transf_function; intros.
  destruct (type_function f) as [env|] eqn:TY; try discriminate.
  destruct (regalloc f); try discriminate.
  destruct (check_function f f0 env) as [] eqn:?; inv H.
  unfold check_function in Heqr.
  destruct (analyze f env (pair_codes f tf)) as [an|] eqn:?; try discriminate.
  monadInv Heqr.
  destruct (check_entrypoints_aux f tf env x) as [y|] eqn:?; try discriminate.
  unfold check_entrypoints_aux, pair_entrypoints in Heqo0. MonadInv.
  exploit extract_moves_sound; eauto. intros [A B]. subst b.
  exploit check_succ_sound; eauto. intros [k EQ1]. subst b0.
  econstructor; eauto. eapply type_function_correct; eauto. congruence.
Qed.

Lemma invert_code:
  forall f env tf pc i opte e,
  wt_function f env ->
  (RTL_memsem.fn_code f)!pc = Some i ->
  transfer f env (pair_codes f tf) pc opte = OK e ->
  exists eafter, exists bsh, exists bb,
  opte = OK eafter /\
  (pair_codes f tf)!pc = Some bsh /\
  (LTL_memsem.fn_code tf)!pc = Some bb /\
  expand_block_shape bsh i bb /\
  transfer_aux f env bsh eafter = Some e /\
  wt_instr f env i.
Proof.
  intros. destruct opte as [eafter|]; simpl in H1; try discriminate. exists eafter.
  destruct (pair_codes f tf)!pc as [bsh|] eqn:?; try discriminate. exists bsh.
  exploit matching_instr_block; eauto. intros [bb [A B]].
  destruct (transfer_aux f env bsh eafter) as [e1|] eqn:?; inv H1.
  exists bb. exploit wt_instr_at; eauto.
  tauto.
Qed.

(** * Semantic preservation *)

Section PRESERVATION.

Variable prog: RTL_memsem.program.
Variable tprog: LTL_memsem.program.
Hypothesis TRANSF: match_prog prog tprog.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_match TRANSF).

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof (Genv.senv_match TRANSF).

Lemma functions_translated:
  forall (v: val) (f: RTL_memsem.fundef),
  Genv.find_funct ge v = Some f ->
  exists tf,
  Genv.find_funct tge v = Some tf /\ transf_fundef f = OK tf.
Proof (Genv.find_funct_transf_partial TRANSF).

Lemma function_ptr_translated:
  forall (b: block) (f: RTL_memsem.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists tf,
  Genv.find_funct_ptr tge b = Some tf /\ transf_fundef f = OK tf.
Proof (Genv.find_funct_ptr_transf_partial TRANSF).

Lemma sig_function_translated:
  forall f tf,
  transf_fundef f = OK tf ->
  LTL_memsem.funsig tf = RTL_memsem.funsig f.
Proof.
  intros; destruct f; monadInv H.
  destruct (transf_function_inv _ _ EQ). simpl; auto.
  auto.
Qed.

Lemma find_function_translated:
  forall ros rs fd ros' e e' ls,
  RTL_memsem.find_function ge ros rs = Some fd ->
  add_equation_ros ros ros' e = Some e' ->
  satisf rs ls e' ->
  exists tfd,
  LTL_memsem.find_function tge ros' ls = Some tfd /\ transf_fundef fd = OK tfd.
Proof.
  unfold RTL_memsem.find_function, LTL_memsem.find_function; intros.
  destruct ros as [r|id]; destruct ros' as [r'|id']; simpl in H0; MonadInv.
  (* two regs *)
  exploit add_equation_lessdef; eauto. intros LD. inv LD.
  eapply functions_translated; eauto.
  rewrite <- H2 in H. simpl in H. congruence.
  (* two symbols *)
  rewrite symbols_preserved. rewrite Heqo.
  eapply function_ptr_translated; eauto.
Qed.

(*CompComp adaptation: state refactoring, added retty, 
 ported star -> effstep_star*)
Lemma exec_moves:
  forall mv env rs s f sp bb m e e' ls retty,
  track_moves env mv e = Some e' ->
  wf_moves mv ->
  satisf rs ls e' ->
  wt_regset env rs ->
  exists ls',
    effstep_star LTL_eff_sem tge EmptyEffect (Block s f sp (expand_moves mv bb) ls retty) m
               (*E0*) (Block s f sp bb ls' retty) m
  /\ satisf rs ls' e.
Proof.
Opaque destroyed_by_op.
  induction mv; simpl; intros.
  (* base *)
- unfold expand_moves; simpl. inv H. exists ls; split. apply effstep_star_zero. auto.
  (* step *)
- destruct a as [src dst]. unfold expand_moves. simpl.
  destruct (track_moves env mv e) as [e1|] eqn:?; MonadInv.
  assert (wf_moves mv). red; intros. apply H0; auto with coqlib.
  destruct src as [rsrc | ssrc]; destruct dst as [rdst | sdst].
  (* reg-reg *)
+ exploit IHmv; eauto. eapply subst_loc_undef_satisf; eauto.
  intros [ls' [A B]]. exists ls'; split; auto. eapply effstep_star_trans'; eauto.
  apply effstep_star_one. econstructor. simpl. eauto. auto.
  reflexivity.
  (* reg->stack *)
+ exploit IHmv; eauto. eapply subst_loc_undef_satisf; eauto.
  intros [ls' [A B]]. exists ls'; split; auto. eapply effstep_star_trans'; eauto.
  apply effstep_star_one. econstructor. simpl. eauto.
  reflexivity. 
  (* stack->reg *)
+ simpl in Heqb. exploit IHmv; eauto. eapply subst_loc_undef_satisf; eauto.
  intros [ls' [A B]]. exists ls'; split; auto. eapply effstep_star_trans'; eauto.
  apply effstep_star_one. econstructor. auto.
  reflexivity. 
  (* stack->stack *)
+ exploit H0; auto with coqlib. unfold wf_move. tauto.
Qed.

(** The simulation relation *)

(*CompComp adaptation: state refactoring, added retty, 
 ported star -> effstep_star, added L, ensured L sp= true*)
Inductive match_stackframes (L:block -> bool): list RTL_memsem.stackframe -> list LTL_memsem.stackframe -> signature -> Prop :=
  | match_stackframes_nil: forall sg,
      (*compcomp: drop this condition sg.(sig_res) = Some Tint ->*)
      match_stackframes L nil nil sg
  | match_stackframes_cons:
      forall res f sp pc rs s tf bb ls ts sg an e env 
        (STACKS: match_stackframes L s ts (fn_sig tf))
        (FUN: transf_function f = OK tf)
        (ANL: analyze f env (pair_codes f tf) = Some an)
        (EQ: transfer f env (pair_codes f tf) pc an!!pc = OK e)
        (WTF: wt_function f env)
        (WTRS: wt_regset env rs)
        (WTRES: env res = proj_sig_res sg)
        (STEPS: forall v ls1 m retty,
           Val.lessdef v (Locmap.getpair (map_rpair R (loc_result sg)) ls1) ->
           Val.has_type v (env res) ->
           agree_callee_save ls ls1 ->
           exists ls2,
           effstep_star LTL_eff_sem tge EmptyEffect
                                 (Block ts tf sp bb ls1 retty) m
                          (*E0*) (State ts tf sp pc ls2 retty) m
           /\ satisf (rs#res <- v) ls2 e)
        (*new:*) (Lsp: exists b z, sp = Vptr b z /\ L b = true),
      match_stackframes L
        (RTL_memsem.Stackframe res f sp pc rs :: s)
        (LTL_memsem.Stackframe tf sp ls bb :: ts)
        sg.

 (*CompComp?  NEW INVARIANT: 
       if stack is empty, then
         either tf is tailcallable, or retty=sig_res (fn_sig tf)
 *)

Fixpoint last_frame (s: list RTL_memsem.stackframe) := 
  match s with 
    | nil => nil
    | RTL_memsem.Stackframe _ _ _ _ _ :: nil => s
    | _ :: s => last_frame s
  end.

Definition agree_retty (s: list RTL_memsem.stackframe) (retty: option typ) := 
  match last_frame s with
    | RTL_memsem.Stackframe res caller sp pc rs :: nil => sig_res (RTL_memsem.fn_sig caller)=retty
    | _ => True
  end.

(*CompComp adaptation: state refactoring, added retty and L*)
Inductive match_states (L:block -> bool): RTL_memsem.state -> mem -> LTL_memsem.state -> mem -> Prop :=
  | match_states_intro:
      forall s f sp pc rs m ts tf ls m' an e env retty
        (STACKS: match_stackframes L s ts (fn_sig tf))
        (FUN: transf_function f = OK tf)
        (ANL: analyze f env (pair_codes f tf) = Some an)
        (EQ: transfer f env (pair_codes f tf) pc an!!pc = OK e)
        (SAT: satisf rs ls e)
        (MEM: Mem.extends m m')
        (WTF: wt_function f env)
        (WTRS: wt_regset env rs)
      (*Compcomp: new hypotheses:*)
        (AGRTY: agree_retty s retty) 
        (AGNIL: s=nil -> sig_res (RTL_memsem.fn_sig f)=retty)
        (Lsp: exists b z, sp = Vptr b z /\ L b = true),
      match_states L (RTL_memsem.State s f sp pc rs) m
                     (LTL_memsem.State ts tf sp pc ls retty) m'
  | match_states_call:
      forall s f args m ts tf ls m' retty
        (STACKS: match_stackframes L s ts (funsig tf))
        (FUN: transf_fundef f = OK tf)
        (ARGS: Val.lessdef_list args (map (fun p => Locmap.getpair p ls) (loc_arguments (funsig tf))))
        (AG: agree_callee_save (parent_locset ts) ls)
        (MEM: Mem.extends m m')
        (WTARGS: Val.has_type_list args (sig_args (funsig tf)))
      (*Compcomp: new hypotheses:*)
        (AGRTY: agree_retty s retty) 
        (AGNIL: s=nil -> sig_res (RTL_memsem.funsig f)=retty),
      match_states L (RTL_memsem.Callstate s f args) m
                     (LTL_memsem.Callstate ts tf ls retty) m'
  | match_states_return:
      forall s res m ts ls m' sg retty
        (STACKS: match_stackframes L s ts sg)
        (RES: Val.lessdef res (Locmap.getpair (map_rpair R (loc_result sg)) ls))
        (AG: agree_callee_save (parent_locset ts) ls)
        (MEM: Mem.extends m m')
        (WTRES: Val.has_type res (proj_sig_res sg))
      (*Compcomp: new hypotheses:*)
        (AGRTY: agree_retty s retty) 
        (AGNIL: s=nil -> sig_res sg=retty),
      match_states L (RTL_memsem.Returnstate s res) m
                     (LTL_memsem.Returnstate ts ls retty) m'.

Lemma match_stackframes_change_sig:
  forall L s ts sg sg',
  match_stackframes L s ts sg ->
  sg'.(sig_res) = sg.(sig_res) ->
  match_stackframes L s ts sg'.
Proof.
  intros. inv H.
  constructor. (* congruence.*)
  econstructor; eauto.
  unfold proj_sig_res in *. rewrite H0; auto.
  intros. unfold loc_result in H; rewrite H0 in H; eauto.
Qed.

Ltac UseShape :=
  match goal with
  | [ WT: wt_function _ _, CODE: (RTL_memsem.fn_code _)!_ = Some _, EQ: transfer _ _ _ _ _ = OK _ |- _ ] =>
      destruct (invert_code _ _ _ _ _ _ _ WT CODE EQ) as (eafter & bsh & bb & AFTER & BSH & TCODE & EBS & TR & WTI);
      inv EBS; unfold transfer_aux in TR; MonadInv
  end.

Remark addressing_not_long:
  forall env f addr args dst s r,
  wt_instr f env (Iload Mint64 addr args dst s) ->
  In r args -> r <> dst.
Proof.
  intros.
  assert (forall ty, In ty (type_of_addressing addr) -> ty = Tint).
  { intros. destruct addr; simpl in H1; intuition. }
  inv H.
  assert (env r = Tint).
  { generalize args (type_of_addressing addr) H0 H1 H5.
    induction args0; simpl; intros.
    contradiction.
    destruct l. discriminate. inv H4.
    destruct H2. subst a. apply H3; auto with coqlib.
    eauto with coqlib.
  }
  red; intros; subst r. rewrite H in H8; discriminate.
Qed.

(** The proof of semantic preservation is a simulation argument of the
    "plus" kind. *)

Lemma match_states_extends L c1 m1 c2 m2 (H: match_states L c1 m1 c2 m2): Mem.extends m1 m2.
Proof. destruct H; trivial. Qed.

Lemma match_stackframes_sub: forall L s s' sg (MS: match_stackframes L s s' sg)
  L' (HL: forall b, L b = true -> L' b = true), match_stackframes L' s s' sg.
Proof.
  induction 1; simpl; intros; econstructor; eauto.
  destruct Lsp as [b [z [HSP Hb]]]. subst. apply HL in Hb. exists b, z; split; trivial.
Qed.
(*
Lemma add_equations_builtin_args_LD: forall args args' e e1 e2,
  add_equations_builtin_args e args args' e1 = Some e2 ->
  Val.list_
*)
(*CompComp adptation: state refactoring, elimination of trace t*)
Lemma core_diagram:
  forall U S1 m1 S2 m2 , RTL_memsem.estep ge U S1 m1 S2 m2 -> wt_state S1 m1 ->
  forall L S1' m1', match_states L S1 m1 S1' m1' ->
  exists S2' m2' U', effstep_plus LTL_eff_sem tge U' S1' m1' S2' m2' /\ 
                     match_states (fun b : block => L b || freshblock m1' m2' b) S2 m2 S2' m2' /\
                    (forall b ofs, U' b ofs = true -> L b = true \/ U b ofs = true).
Proof.
  induction 1; intros WT L S1' m1' MS; inv MS; try UseShape.

(* nop *)
- exploit exec_moves; eauto. intros [ls1 [X Y]].
  eexists; eexists; econstructor. split; [| split]. 
  * eapply effstep_one_star_one_plus.
    econstructor; eauto.
    eexact X.
    econstructor; eauto. reflexivity.
  * exploit satisf_successors; eauto. simpl; eauto. intros [enext [U V]].
    econstructor; eauto. 
    eapply match_stackframes_sub; try eassumption. intros b Hb; rewrite Hb; trivial.
    destruct Lsp as [b [z [Hsp Hb]]]. subst. exists b, z; rewrite Hb; split; trivial.
  * discriminate.

(* op move *)
- generalize (wt_exec_Iop _ _ _ _ _ _ _ _ _ _ _ WTI H0 WTRS). intros WTRS'.
  simpl in H0. inv H0.
  exploit (exec_moves mv); eauto. intros [ls1 [X Y]].
  eexists; eexists; econstructor; split; [| split]. 
  * eapply effstep_one_star_one_plus.
    econstructor; eauto.
    eexact X. 
    econstructor; eauto. reflexivity.
  * exploit satisf_successors; eauto. simpl; eauto. eapply subst_reg_satisf; eauto.
    intros [enext [U V]].
    econstructor; eauto.
    eapply match_stackframes_sub; try eassumption. intros b Hb; rewrite Hb; trivial.
    destruct Lsp as [b [z [Hsp Hb]]]. subst. exists b, z; rewrite Hb; split; trivial.
  * discriminate.

(* op makelong *)
- generalize (wt_exec_Iop _ _ _ _ _ _ _ _ _ _ _ WTI H0 WTRS). intros WTRS'.
  simpl in H0. inv H0.
  exploit (exec_moves mv); eauto. intros [ls1 [X Y]].
  eexists; eexists; econstructor; split; [| split].
  * eapply effstep_one_star_one_plus.
    econstructor; eauto.
    eexact X. 
    econstructor; eauto. reflexivity.
  * exploit satisf_successors; eauto. simpl; eauto.
    eapply subst_reg_kind_satisf_makelong. eauto. eauto.
    intros [enext [U V]].
    econstructor; eauto.
    eapply match_stackframes_sub; try eassumption. intros b Hb; rewrite Hb; trivial.
    destruct Lsp as [b [z [Hsp Hb]]]. subst. exists b, z; rewrite Hb; split; trivial.
  * discriminate.

(* op lowlong *)
- generalize (wt_exec_Iop _ _ _ _ _ _ _ _ _ _ _ WTI H0 WTRS). intros WTRS'.
  simpl in H0. inv H0.
  exploit (exec_moves mv); eauto. intros [ls1 [X Y]].
  eexists; eexists; econstructor; split; [| split].
  * eapply effstep_one_star_one_plus.
    econstructor; eauto.
    eexact X. 
    econstructor; eauto. reflexivity.
  * exploit satisf_successors; eauto. simpl; eauto.
    eapply subst_reg_kind_satisf_lowlong. eauto. eauto.
    intros [enext [U V]].
    econstructor; eauto.
    eapply match_stackframes_sub; try eassumption. intros b Hb; rewrite Hb; trivial.
    destruct Lsp as [b [z [Hsp Hb]]]. subst. exists b, z; rewrite Hb; split; trivial.
  * discriminate.

(* op highlong *)
- generalize (wt_exec_Iop _ _ _ _ _ _ _ _ _ _ _ WTI H0 WTRS). intros WTRS'.
  simpl in H0. inv H0.
  exploit (exec_moves mv); eauto. intros [ls1 [X Y]].
  eexists; eexists; econstructor; split; [| split].
  * eapply effstep_one_star_one_plus.
    econstructor; eauto.
    eexact X. 
    econstructor; eauto. reflexivity.
  * exploit satisf_successors; eauto. simpl; eauto.
    eapply subst_reg_kind_satisf_highlong. eauto. eauto.
    intros [enext [U V]].
    econstructor; eauto.
    eapply match_stackframes_sub; try eassumption. intros b Hb; rewrite Hb; trivial.
    destruct Lsp as [b [z [Hsp Hb]]]. subst. exists b, z; rewrite Hb; split; trivial.
  * discriminate.

(* op regular *)
- generalize (wt_exec_Iop _ _ _ _ _ _ _ _ _ _ _ WTI H0 WTRS). intros WTRS'.
  exploit (exec_moves mv1); eauto. intros [ls1 [A1 B1]].
  exploit transfer_use_def_satisf; eauto. intros [X Y].
  exploit eval_operation_lessdef; eauto. intros [v' [F G]].
  exploit (exec_moves mv2); eauto. intros [ls2 [A2 B2]].
  eexists; eexists; econstructor; split; [|split].
  * eapply effstep_one_star_one_star_one_plus.
    econstructor; eauto.
    eexact A1. 
    econstructor. instantiate (1 := v'). rewrite <- F.
      apply eval_operation_preserved. exact symbols_preserved.
      eauto.
    eexact A2.
    constructor. reflexivity.
  * exploit satisf_successors; eauto. simpl; eauto. intros [enext [U V]].
    econstructor; eauto.
    eapply match_stackframes_sub; try eassumption. intros b Hb; rewrite Hb; trivial.
    destruct Lsp as [b [z [Hsp Hb]]]. subst. exists b, z; rewrite Hb; split; trivial.
  * discriminate.

(* op dead *)
- exploit exec_moves; eauto. intros [ls1 [X Y]].
  eexists; eexists; econstructor; split; [| split].
  * eapply effstep_one_star_one_plus.
    econstructor; eauto.
    eexact X. 
    econstructor; eauto. reflexivity.
  * exploit satisf_successors. eauto. eauto. simpl; eauto. eauto.
    eapply reg_unconstrained_satisf; eauto.
    intros [enext [U V]].
    econstructor; eauto.
    eapply match_stackframes_sub; try eassumption. intros b Hb; rewrite Hb; trivial.
    eapply wt_exec_Iop; eauto.
    destruct Lsp as [b [z [Hsp Hb]]]. subst. exists b, z; rewrite Hb; split; trivial.
  * discriminate.

(* load regular *)
- generalize (wt_exec_Iload _ _ _ _ _ _ _ _ _ _ _ WTI H1 WTRS). intros WTRS'.
  exploit (exec_moves mv1); eauto. intros [ls1 [A1 B1]].
  exploit transfer_use_def_satisf; eauto. intros [X Y].
  exploit eval_addressing_lessdef; eauto. intros [a' [F G]].
  exploit Mem.loadv_extends; eauto. intros [v' [P Q]].
  exploit (exec_moves mv2); eauto. intros [ls2 [A2 B2]].
  eexists; eexists; econstructor; split; [| split].
  * eapply effstep_one_star_one_star_one_plus.
    econstructor; eauto.
    eexact A1. 
    econstructor. instantiate (1 := a'). rewrite <- F.
      apply eval_addressing_preserved. exact symbols_preserved. eauto. eauto.
    eexact A2.
    constructor. reflexivity.
  * exploit satisf_successors; eauto. simpl; eauto. intros [enext [U V]].
    econstructor; eauto.
    eapply match_stackframes_sub; try eassumption. intros b Hb; rewrite Hb; trivial.
    destruct Lsp as [b [z [Hsp Hb]]]. subst. exists b, z; rewrite Hb; split; trivial.
  * discriminate.

(* load pair *)
- generalize (wt_exec_Iload _ _ _ _ _ _ _ _ _ _ _ WTI H1 WTRS). intros WTRS'.
  exploit loadv_int64_split; eauto. intros (v1 & v2 & LOAD1 & LOAD2 & V1 & V2).
  set (v2' := if Archi.big_endian then v2 else v1) in *.
  set (v1' := if Archi.big_endian then v1 else v2) in *.
  exploit (exec_moves mv1); eauto. intros [ls1 [A1 B1]].
  assert (LD1: Val.lessdef_list rs##args (reglist ls1 args1')).
  { eapply add_equations_lessdef; eauto. }
  exploit eval_addressing_lessdef. eexact LD1. eauto. intros [a1' [F1 G1]].
  exploit Mem.loadv_extends. eauto. eexact LOAD1. eexact G1. intros (v1'' & LOAD1' & LD2).
  set (ls2 := Locmap.set (R dst1') v1'' (undef_regs (destroyed_by_load Mint32 addr) ls1)).
  assert (SAT2: satisf (rs#dst <- v) ls2 e2).
  { eapply loc_unconstrained_satisf. eapply can_undef_satisf; eauto.
    eapply reg_unconstrained_satisf. eauto.
    eapply add_equations_satisf; eauto. assumption.
    rewrite Regmap.gss. apply Val.lessdef_trans with v1'; auto.
  }
  exploit (exec_moves mv2); eauto. intros [ls3 [A3 B3]].
  assert (LD3: Val.lessdef_list rs##args (reglist ls3 args2')).
  { replace (rs##args) with ((rs#dst<-v)##args).
    eapply add_equations_lessdef; eauto.
    apply list_map_exten; intros. rewrite Regmap.gso; auto.
    eapply addressing_not_long; eauto.
  }
  exploit eval_addressing_lessdef. eexact LD3.
  eapply eval_offset_addressing; eauto. intros [a2' [F2 G2]].
  exploit Mem.loadv_extends. eauto. eexact LOAD2. eexact G2. intros (v2'' & LOAD2' & LD4).
  set (ls4 := Locmap.set (R dst2') v2'' (undef_regs (destroyed_by_load Mint32 addr2) ls3)).
  assert (SAT4: satisf (rs#dst <- v) ls4 e0).
  { eapply loc_unconstrained_satisf. eapply can_undef_satisf; eauto.
    eapply add_equations_satisf; eauto. assumption.
    rewrite Regmap.gss. apply Val.lessdef_trans with v2'; auto.
  }
  exploit (exec_moves mv3); eauto. intros [ls5 [A5 B5]].
  eexists; eexists; econstructor; split; [| split].
  * eapply effstep_one_star_one_star_one_plus.
    + econstructor; eauto.
    + eexact A1.
    + econstructor.
      instantiate (1 := a1'). rewrite <- F1. apply eval_addressing_preserved. exact symbols_preserved.
      eexact LOAD1'. instantiate (1 := ls2); auto.
    + eapply effstep_star_trans. eexact A3. 
      eapply effstep_star_trans. 
        eapply effstep_star_one.
        econstructor.
        instantiate (1 := a2'). rewrite <- F2. apply eval_addressing_preserved. exact symbols_preserved.
        eexact LOAD2'. instantiate (1 := ls4); auto.
      eexact A5.
    + constructor.
    + reflexivity.
  * exploit satisf_successors; eauto. simpl; eauto. intros [enext [W Z]].
    econstructor; eauto.
    eapply match_stackframes_sub; try eassumption. intros b Hb; rewrite Hb; trivial.
    destruct Lsp as [b [z [Hsp Hb]]]. subst. exists b, z; rewrite Hb; split; trivial.
  * discriminate.
  

(* load first word of a pair *)
- generalize (wt_exec_Iload _ _ _ _ _ _ _ _ _ _ _ WTI H1 WTRS). intros WTRS'.
  exploit loadv_int64_split; eauto. intros (v1 & v2 & LOAD1 & LOAD2 & V1 & V2).
  set (v2' := if Archi.big_endian then v2 else v1) in *.
  set (v1' := if Archi.big_endian then v1 else v2) in *.
  exploit (exec_moves mv1); eauto. intros [ls1 [A1 B1]].
  assert (LD1: Val.lessdef_list rs##args (reglist ls1 args')).
  { eapply add_equations_lessdef; eauto. }
  exploit eval_addressing_lessdef. eexact LD1. eauto. intros [a1' [F1 G1]].
  exploit Mem.loadv_extends. eauto. eexact LOAD1. eexact G1. intros (v1'' & LOAD1' & LD2).
  set (ls2 := Locmap.set (R dst') v1'' (undef_regs (destroyed_by_load Mint32 addr) ls1)).
  assert (SAT2: satisf (rs#dst <- v) ls2 e0).
  { eapply parallel_assignment_satisf; eauto.
    apply Val.lessdef_trans with v1'; auto.
    eapply can_undef_satisf. eauto. eapply add_equations_satisf; eauto.
  }
  exploit (exec_moves mv2); eauto. intros [ls3 [A3 B3]].
  eexists; eexists; econstructor; split; [|split].
  * eapply effstep_one_star_one_star_one_plus.
    econstructor; eauto.
    eexact A1. 
    econstructor.
      instantiate (1 := a1'). rewrite <- F1. apply eval_addressing_preserved. exact symbols_preserved.
      eexact LOAD1'. instantiate (1 := ls2); auto.
    eexact A3.
    constructor. reflexivity.
  * exploit satisf_successors; eauto. simpl; eauto. intros [enext [W Z]].
    econstructor; eauto.
    eapply match_stackframes_sub; try eassumption. intros b Hb; rewrite Hb; trivial.
    destruct Lsp as [b [z [Hsp Hb]]]. subst. exists b, z; rewrite Hb; split; trivial.
  * discriminate.

(* load second word of a pair *)
- generalize (wt_exec_Iload _ _ _ _ _ _ _ _ _ _ _ WTI H1 WTRS). intros WTRS'.
  exploit loadv_int64_split; eauto. intros (v1 & v2 & LOAD1 & LOAD2 & V1 & V2).
  set (v2' := if Archi.big_endian then v2 else v1) in *.
  set (v1' := if Archi.big_endian then v1 else v2) in *.
  exploit (exec_moves mv1); eauto. intros [ls1 [A1 B1]].
  assert (LD1: Val.lessdef_list rs##args (reglist ls1 args')).
  { eapply add_equations_lessdef; eauto. }
  exploit eval_addressing_lessdef. eexact LD1.
  eapply eval_offset_addressing; eauto. intros [a1' [F1 G1]].
  exploit Mem.loadv_extends. eauto. eexact LOAD2. eexact G1. intros (v2'' & LOAD2' & LD2).
  set (ls2 := Locmap.set (R dst') v2'' (undef_regs (destroyed_by_load Mint32 addr2) ls1)).
  assert (SAT2: satisf (rs#dst <- v) ls2 e0).
  { eapply parallel_assignment_satisf; eauto.
    apply Val.lessdef_trans with v2'; auto.
    eapply can_undef_satisf. eauto. eapply add_equations_satisf; eauto.
  }
  exploit (exec_moves mv2); eauto. intros [ls3 [A3 B3]].
  eexists; eexists; econstructor; split; [|split].
  * eapply effstep_one_star_one_star_one_plus.
    econstructor; eauto.
    eexact A1.
    econstructor.
     instantiate (1 := a1'). rewrite <- F1. apply eval_addressing_preserved. exact symbols_preserved.
     eexact LOAD2'. instantiate (1 := ls2); auto.
    eexact A3.
    constructor. reflexivity.
  * exploit satisf_successors; eauto. simpl; eauto. intros [enext [W Z]].
    econstructor; eauto.
    eapply match_stackframes_sub; try eassumption. intros b Hb; rewrite Hb; trivial.
    destruct Lsp as [b [z [Hsp Hb]]]. subst. exists b, z; rewrite Hb; split; trivial.
  * discriminate.

(* load dead *)
- exploit exec_moves; eauto. intros [ls1 [X Y]].
  eexists; eexists; econstructor; split; [|split].
  * eapply effstep_one_star_one_plus.
    econstructor; eauto.
    eexact X.
    econstructor; eauto. reflexivity.
  * exploit satisf_successors. eauto. eauto. simpl; eauto. eauto.
    eapply reg_unconstrained_satisf; eauto.
    intros [enext [U V]].
    econstructor; eauto.
    eapply match_stackframes_sub; try eassumption. intros b Hb; rewrite Hb; trivial.
    eapply wt_exec_Iload; eauto.
    destruct Lsp as [b [z [Hsp Hb]]]. subst. exists b, z; rewrite Hb; split; trivial.
  * discriminate.

(* store *)
- exploit exec_moves; eauto. intros [ls1 [X Y]].
  exploit add_equations_lessdef; eauto. intros LD. simpl in LD. inv LD.
  exploit eval_addressing_lessdef; eauto. intros [a' [F G]].
  exploit Mem.storev_extends; eauto. intros [m'' [P Q]].
  eexists; eexists; econstructor; split; [|split].
  * eapply effstep_one_star_one_plus.
    econstructor; eauto.
    eapply effstep_star_trans. eexact X.
    eapply effstep_star_one. econstructor. instantiate (1 := a'). rewrite <- F.
      apply eval_addressing_preserved. exact symbols_preserved. eauto. eauto.
    constructor. reflexivity.
  * exploit satisf_successors; eauto. simpl; eauto.
    eapply can_undef_satisf; eauto. eapply add_equations_satisf; eauto. intros [enext [U V]].
    econstructor; eauto.
    eapply match_stackframes_sub; try eassumption. intros b Hb; rewrite Hb; trivial.
    destruct Lsp as [b [z [Hsp Hb]]]. subst. exists b, z; rewrite Hb; split; trivial.
  * simpl; intros. rewrite orb_false_r in H2.
    apply andb_true_iff in H2. destruct H2.
    apply andb_true_iff in H2. destruct H2.
    eapply StoreEffect_propagate_ext; eauto. 

(* store 2 *)
- exploit Mem.storev_int64_split; eauto.
  replace (if Archi.big_endian then Val.hiword rs#src else Val.loword rs#src)
     with (sel_val kind_first_word rs#src)
       by (unfold kind_first_word; destruct Archi.big_endian; reflexivity).
  replace (if Archi.big_endian then Val.loword rs#src else Val.hiword rs#src)
     with (sel_val kind_second_word rs#src)
       by (unfold kind_second_word; destruct Archi.big_endian; reflexivity).
  intros [m1 [STORE1 STORE2]].
  exploit (exec_moves mv1); eauto. intros [ls1 [X Y]].
  exploit add_equations_lessdef. eexact Heqo1. eexact Y. intros LD1.
  exploit add_equation_lessdef. eapply add_equations_satisf. eexact Heqo1. eexact Y.
  simpl. intros LD2.
  set (ls2 := undef_regs (destroyed_by_store Mint32 addr) ls1).
  assert (SAT2: satisf rs ls2 e1).
    eapply can_undef_satisf. eauto.
    eapply add_equation_satisf. eapply add_equations_satisf; eauto.
  exploit eval_addressing_lessdef. eexact LD1. eauto. intros [a1' [F1 G1]].
  assert (F1': eval_addressing tge sp addr (reglist ls1 args1') = Some a1').
    rewrite <- F1. apply eval_addressing_preserved. exact symbols_preserved.
  exploit Mem.storev_extends. eauto. eexact STORE1. eexact G1. eauto.
  intros [m2' [STORE1' EXT1]].
  exploit (exec_moves mv2); eauto. intros [ls3 [U V]].
  exploit add_equations_lessdef. eexact Heqo. eexact V. intros LD3.
  exploit add_equation_lessdef. eapply add_equations_satisf. eexact Heqo. eexact V.
  simpl. intros LD4.
  exploit eval_addressing_lessdef. eexact LD3. eauto. intros [a2' [F2 G2]].
  assert (F2': eval_addressing tge sp addr (reglist ls3 args2') = Some a2').
    rewrite <- F2. apply eval_addressing_preserved. exact symbols_preserved.
  exploit eval_offset_addressing. eauto. eexact F2'. intros F2''.
  exploit Mem.storev_extends. eexact EXT1. eexact STORE2.
  apply Val.add_lessdef. eexact G2. eauto. eauto.
  intros [m3' [STORE2' EXT2]].
  eexists; eexists; econstructor; split; [|split].
  * eapply effstep_one_star_one_star_one_plus.
    econstructor; eauto.
    eexact X.
    econstructor. eexact F1'. eexact STORE1'. instantiate (1 := ls2). auto.
    eapply effstep_star_trans. eexact U. 
      eapply effstep_star_one. econstructor. eexact F2''. eexact STORE2'. eauto.
    constructor. reflexivity.
  * exploit satisf_successors; eauto. simpl; eauto.
    eapply can_undef_satisf. eauto.
    eapply add_equation_satisf. eapply add_equations_satisf; eauto.
    intros [enext [P Q]].
    econstructor; eauto.
    eapply match_stackframes_sub; try eassumption. intros b Hb; rewrite Hb; trivial.
    destruct Lsp as [b [z [Hsp Hb]]]. subst. exists b, z; rewrite Hb; split; trivial.
  * simpl; intros. rewrite orb_false_r in H2.
    apply andb_true_iff in H2. destruct H2.
    apply andb_true_iff in H2. destruct H2. clear H3 H4 X U.
    destruct a; try discriminate. inv G2. inv G1.
    destruct Lsp as [spb [zz [SP Lsp]]]. subst sp.
    remember (StoreEffect (Vptr b0 i) (encode_val Mint32 (ls1 (R src1'))) b ofs) as d1.
    destruct d1; simpl; trivial; apply eq_sym in Heqd1.
    + clear H2.
      apply StoreEffectD in Heqd1. destruct Heqd1 as [ii [VV Arith]]. inv VV. right.
      rewrite encode_val_length in *.
      destruct (eq_block b b); simpl in *; try congruence.
      destruct (zle (Int.unsigned ii) ofs); simpl; try omega.
      destruct (zlt ofs (Int.unsigned ii + 8)); trivial; try omega.
    + simpl in *. right. rewrite encode_val_length in *; simpl in *.
(*      apply Mem.store_valid_access_3 in  H1. simpl in H1. destruct H1 as [VA1 VA2]. unfold align_chunk in VA2. simpl in VA2.
      apply Mem.store_valid_access_3 in STORE2. simpl in STORE2. destruct STORE2 as [VA1' VA2']. unfold align_chunk in VA2'. simpl in VA2'.*)
(*      unfold offset_addressing, offset_addressing_total in H11. simpl in H11. inv H11.
      destruct addr; simpl in *. clear H2 F2'' H0.*)
      apply andb_true_iff in H2. destruct H2.
      apply andb_true_iff in H2. destruct H2. clear F1 F1' F2 F2'.
      destruct (eq_block b0 b); simpl in *; try discriminate. subst b0.
      apply andb_true_iff in H2. destruct H2.
      destruct (zle (Int.unsigned (Int.add i (Int.repr 4))) ofs); try discriminate. clear H2.
      destruct (zlt ofs (Int.unsigned (Int.add i (Int.repr 4)) + 4)); try discriminate. clear H5.
      apply Mem.store_valid_access_3 in  H1. simpl in H1. destruct H1 as [VA1 VA2]. unfold align_chunk in VA2. clear VA1 STORE1 STORE2 STORE2' STORE1' F2'' H0 WT H3 H4 LD3 LD4 EXT2. 
      assert (MAXUNS: Int.max_unsigned = 4294967295) by reflexivity.
      assert (FOUR: Int.unsigned (Int.add i (Int.repr 4)) = Int.unsigned i + 4).
         { rewrite Int.add_unsigned, (Int.unsigned_repr 4). 2: rewrite MAXUNS; omega.
           apply Int.unsigned_repr.
           destruct (Int.unsigned_range_2 i). split. omega. 
           destruct VA2. rewrite H2, MAXUNS in *. omega. }
      rewrite FOUR in *. 
      destruct (zle (Int.unsigned i) ofs); simpl in *; try omega.
      destruct (zlt ofs (Int.unsigned i + 4)); try discriminate. 
      destruct (zlt ofs (Int.unsigned i + 8)); trivial. omega.

(* call *)
- set (sg := RTL_memsem.funsig fd) in *.
  set (args' := loc_arguments sg) in *.
  set (res' := loc_result sg) in *.
  exploit (exec_moves mv1); eauto. intros [ls1 [A1 B1]].
  exploit find_function_translated. eauto. eauto. eapply add_equations_args_satisf; eauto.
  intros [tfd [E F]].
  assert (SIG: funsig tfd = sg). eapply sig_function_translated; eauto.
  eexists; eexists; econstructor; split; [|split].
  * eapply effstep_one_star_one_plus.
    econstructor; eauto.
    eexact A1.
    econstructor; eauto. reflexivity.
  * exploit analyze_successors; eauto. simpl. left; eauto. intros [enext [U V]].
    econstructor; eauto.
    econstructor; eauto.
    eapply match_stackframes_sub; try eassumption. intros b Hb; rewrite Hb; trivial. 
    inv WTI. congruence.
    intros. exploit (exec_moves mv2). eauto. eauto.
    eapply function_return_satisf with (v := v) (ls_before := ls1) (ls_after := ls0); eauto.
    eapply add_equation_ros_satisf; eauto.
    eapply add_equations_args_satisf; eauto.
    congruence.
    apply wt_regset_assign; auto.
    intros [ls2 [A2 B2]].
    exists ls2; split.
    eapply effstep_star_trans'. eexact A2. apply effstep_star_one. constructor. reflexivity.
    apply satisf_incr with eafter; auto.
    destruct Lsp as [b [z [Hsp Hb]]]. subst. exists b, z; rewrite Hb; split; trivial.
    rewrite SIG. eapply add_equations_args_lessdef; eauto.
    inv WTI. rewrite <- H7. apply wt_regset_list; auto.
    simpl. red; auto.
    inv WTI. rewrite SIG. rewrite <- H7. apply wt_regset_list; auto.
    (*CompComp adaptation: new retty clauses:*)
    + red. destruct s. simpl; rewrite AGNIL; trivial. apply AGRTY. 
    + congruence.
  * discriminate.

(* tailcall *)
- set (sg := RTL_memsem.funsig fd) in *.
  set (args' := loc_arguments sg) in *.
  exploit Mem.free_parallel_extends; eauto. intros [m'' [P Q]].
  exploit (exec_moves mv); eauto. intros [ls1 [A1 B1]].
  exploit find_function_translated. eauto. eauto. eapply add_equations_args_satisf; eauto.
  intros [tfd [E F]].
  assert (SIG: funsig tfd = sg). eapply sig_function_translated; eauto.
  eexists; eexists; econstructor; split; [|split].
  * eapply effstep_one_star_one_plus.
    econstructor; eauto.
    exact A1.
    econstructor; eauto.
      rewrite <- E. apply find_function_tailcall; auto.
      replace (fn_stacksize tf) with (RTL_memsem.fn_stacksize f); eauto.
      destruct (transf_function_inv _ _ FUN); auto.
    reflexivity.
  * econstructor; eauto.
    { eapply match_stackframes_sub.
      + eapply match_stackframes_change_sig; eauto. rewrite SIG. rewrite e0. decEq.
        destruct (transf_function_inv _ _ FUN); auto.
      + intros b Hb; rewrite Hb; trivial. }
    rewrite SIG. rewrite return_regs_arg_values; auto. eapply add_equations_args_lessdef; eauto.
    inv WTI. rewrite <- H6. apply wt_regset_list; auto.
    apply return_regs_agree_callee_save.
    rewrite SIG. inv WTI. rewrite <- H6. apply wt_regset_list; auto.
    (*CompComp adaptation: new retty clause:*)
    + intros; subst. rewrite e0. eauto.
  * simpl; intros b z Eff. 
    apply andb_true_iff in Eff; destruct Eff. apply andb_true_iff in H1; destruct H1.
    apply effect_semantics.FreeEffectD in H1. destruct H1 as [FE1 [FE2 FE3]]; subst b.
    left. destruct Lsp as [? [? [LSP Hsp]]]. inv LSP. trivial.

(* builtin *)
- specialize (exec_moves mv1 env rs ts tf sp (Lbuiltin ef args' res' :: expand_moves mv2 (Lbranch pc' :: k)) m1' e2 e ls retty).
  intros [ls1 [A1 B1]]; eauto. 
  exploit add_equations_builtin_eval; eauto.
  intros (C & vargs' & vres' & m'' & D & E & F & G).
  exploit (external_call_symbols_preserved). apply senv_preserved. apply E. clear E. intros E.
  assert (WTRS': wt_regset env (regmap_setres res vres rs)) by (eapply wt_exec_Ibuiltin; eauto).
  set (ls2 := Locmap.setres res' vres' (undef_regs (destroyed_by_builtin ef) ls1)).
  assert (satisf (regmap_setres res vres rs) ls2 e0).
  { eapply parallel_set_builtin_res_satisf; eauto.
    eapply can_undef_satisf; eauto. }
  exploit (exec_moves mv2); eauto. intros [ls3 [A3 B3]].
  eexists; eexists; econstructor; split; [|split].
  * eapply effstep_one_star_one_star_one_plus.
    econstructor; eauto.
    eexact A1.
    econstructor. trivial.
      eapply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
      (*eapply external_call_symbols_preserved. apply senv_preserved. eauto.*) eassumption.
      instantiate (1 := ls2); auto.
    eexact A3.
    econstructor. reflexivity.
  * exploit satisf_successors; eauto. simpl; eauto.
    intros [enext [U V]].
    econstructor; eauto.
    eapply match_stackframes_sub; try eassumption. intros b Hb; rewrite Hb; trivial.
    destruct Lsp as [? [? [SP Lsp]]]. subst sp.
      exists x, x0; rewrite Lsp. split; trivial.
  * simpl; intros. clear A3 A1. apply andb_true_iff in H4; destruct H4.
    apply andb_true_iff in H4; destruct H4. rewrite orb_false_r in H4. right.
    eapply (BuiltinEffects.BuiltinEffects_propagate_extends ge tge); try eassumption.
    destruct ef; try discriminate. simpl in *.
    -- (*EF_free*) exploit (add_equations_builtin_args_lessdef env ge sp rs); eauto.
       intros [vl' [EV LD]].
       exploit eval_builtin_args_determ. apply EV.  apply D. intros; subst vl'; trivial.    
    -- (*EF_memcpy*) exploit (add_equations_builtin_args_lessdef env ge sp rs); eauto.
       intros [vl' [EV LD]].
       exploit eval_builtin_args_determ. apply EV.  apply D. intros; subst vl'; trivial.

(* cond *)
- exploit (exec_moves mv); eauto. intros [ls1 [A1 B1]].
  eexists; eexists; econstructor; split; [|split].
  * eapply effstep_one_star_one_plus.
    econstructor; eauto.
    eexact A1.
    econstructor. eapply eval_condition_lessdef; eauto. eapply add_equations_lessdef; eauto.
      eauto. eauto. reflexivity. 
  * exploit satisf_successors; eauto.
    instantiate (1 := if b then ifso else ifnot). simpl. destruct b; auto.
    eapply can_undef_satisf. eauto. eapply add_equations_satisf; eauto.
    intros [enext [U V]].
    econstructor; eauto.
    eapply match_stackframes_sub. eassumption. intros bb Hb; rewrite Hb; trivial.
    destruct Lsp as [bb [z [SP Lsp]]]; subst. exists bb, z; rewrite Lsp; split; trivial.
  * discriminate. 

(* jumptable *)
- exploit (exec_moves mv); eauto. intros [ls1 [A1 B1]].
  assert (Val.lessdef (Vint n) (ls1 (R arg'))).
    rewrite <- H0. eapply add_equation_lessdef with (q := Eq Full arg (R arg')); eauto.
  inv H2.
  eexists; eexists; econstructor; split; [|split].
  * eapply effstep_one_star_one_plus.
    econstructor; eauto.
    eexact A1.
    econstructor. eauto. eauto. eauto. reflexivity. 
  * exploit satisf_successors; eauto.
    instantiate (1 := pc'). simpl. eapply list_nth_z_in; eauto.
    eapply can_undef_satisf. eauto. eapply add_equation_satisf; eauto.
    intros [enext [U V]].
    econstructor; eauto.
    eapply match_stackframes_sub. eassumption. intros bb Hb; rewrite Hb; trivial.
    destruct Lsp as [bb [z [SP Lsp]]]; subst. exists bb, z; rewrite Lsp; split; trivial.
  * discriminate. 

(* return *)
- destruct (transf_function_inv _ _ FUN).
  exploit Mem.free_parallel_extends; eauto. rewrite H10. intros [m'' [P Q]].
  inv WTI; MonadInv.
+ (* without an argument *)
  exploit (exec_moves mv); eauto. intros [ls1 [A1 B1]].
  eexists; eexists; econstructor; split; [|split].
  * eapply effstep_one_star_one_plus.
    econstructor; eauto.
    eexact A1.
    econstructor. eauto. reflexivity. 
  * simpl. econstructor; eauto.
    eapply match_stackframes_sub. rewrite H11; eassumption. intros bb Hb; rewrite Hb; trivial.
    apply return_regs_agree_callee_save.
    constructor. 
  * simpl; intros bb z Eff. 
    apply andb_true_iff in Eff; destruct Eff. 
    apply andb_true_iff in H12; destruct H12.
    apply FreeEffectD in H12. destruct H12 as [FE1 [FE2 FE3]]; subst stk.
    destruct Lsp as [b [ofs [SP Lsp]]]. inv SP; left; trivial.
  
+ (* with an argument *)
  exploit (exec_moves mv); eauto. intros [ls1 [A1 B1]].
  eexists; eexists; econstructor; split; [|split].
  * eapply effstep_one_star_one_plus.
    econstructor; eauto.
    eexact A1.
    econstructor. eauto. reflexivity. 
  * simpl. econstructor; eauto. (* rewrite <- H11.*)
    eapply match_stackframes_sub. rewrite H11; eassumption. intros bb Hb; rewrite Hb; trivial.    
    replace (Locmap.getpair (map_rpair R (loc_result (RTL_memsem.fn_sig f)))
                            (return_regs (parent_locset ts) ls1))
    with (Locmap.getpair (map_rpair R (loc_result (RTL_memsem.fn_sig f))) ls1).
    eapply add_equations_res_lessdef; eauto.
    rewrite H13. apply WTRS.
    generalize (loc_result_caller_save (RTL_memsem.fn_sig f)). 
    destruct (loc_result (RTL_memsem.fn_sig f)); simpl.
    intros A; rewrite A; auto.
    intros [A B]; rewrite A, B; auto.
    apply return_regs_agree_callee_save.
    unfold proj_sig_res. rewrite H13. apply WTRS.
  * simpl; intros bb z Eff. 
    apply andb_true_iff in Eff; destruct Eff. 
    apply andb_true_iff in H12; destruct H12.
    apply FreeEffectD in H12. destruct H12 as [FE1 [FE2 FE3]]; subst stk.
    destruct Lsp as [b [ofs [SP Lsp]]]. inv SP; left; trivial.

(* internal function *)
- monadInv FUN. simpl in *.
  destruct (transf_function_inv _ _ EQ).
  exploit Mem.alloc_extends; eauto. apply Zle_refl. rewrite H8; apply Zle_refl.
  intros [m'' [U V]].
  assert (WTRS: wt_regset env (init_regs args (fn_params f))).
  { apply wt_init_regs. inv H0. rewrite wt_params. rewrite H9. auto. }
  exploit (exec_moves mv). eauto. eauto.
    eapply can_undef_satisf; eauto. eapply compat_entry_satisf; eauto.
    rewrite call_regs_param_values. eexact ARGS.
    exact WTRS.
  intros [ls1 [A B]].
  eexists; eexists; econstructor; split; [|split].
  * eapply effstep_one_star_one_plus.
    econstructor; eauto.
    eapply effstep_star_trans.
      eapply effstep_star_one. econstructor; eauto.
      eexact A.
    econstructor; eauto. reflexivity.
  * econstructor; eauto.
    eapply match_stackframes_sub; try eassumption. intros bb Hb; rewrite Hb; trivial.
    exists stk, Int.zero. erewrite freshblock_alloc; try eassumption. split. trivial. 
     destruct (eq_block stk stk); try congruence; simpl. apply orb_true_r.
  * discriminate. 

(* external function *)
- exploit external_call_mem_extends; eauto. intros [v' [m'' [F [G [J K]]]]].
  simpl in FUN; inv FUN.
  exploit (external_call_symbols_preserved). apply senv_preserved. apply F. clear F. intros F.
  eexists; eexists; econstructor; split; [|split].
  * apply effstep_plus_one. econstructor; eauto.
    (*eapply external_call_symbols_preserved with (ge1 := ge); eauto. apply senv_preserved.*)
  * econstructor; eauto. 
    eapply match_stackframes_sub; try eassumption. intros bb Hb; rewrite Hb; trivial.
    simpl. destruct (loc_result (ef_sig ef)) eqn:RES; simpl.
    rewrite Locmap.gss; auto.
    generalize (loc_result_pair (ef_sig ef)); rewrite RES; intros (A & B & C & D). 
    exploit external_call_well_typed; eauto. unfold proj_sig_res; rewrite B. intros WTRES'.
    rewrite Locmap.gss. rewrite Locmap.gso by (red; auto). rewrite Locmap.gss. 
    rewrite val_longofwords_eq by auto. auto.
    red; intros. rewrite (AG l); trivial.
    symmetry; apply Locmap.gpo. 
    assert (X: forall r, is_callee_save r = false -> Loc.diff l (R r)).
    { intros. destruct l; simpl in *. congruence. auto. }
    generalize (loc_result_caller_save (ef_sig ef)). destruct (loc_result (ef_sig ef)); simpl; intuition auto.
    eapply external_call_well_typed; eauto.
  * simpl; intros bb z Eff. right.
    eapply (BuiltinEffects.BuiltinEffects_propagate_extends ge tge); try eassumption.
(* return *)
- inv STACKS. 
  exploit (STEPS vres ls m1' retty); eauto. rewrite WTRES0; auto. intros [ls2 [A B]].
  eexists; eexists; econstructor; split; [|split].
  * eapply effstep_plus_star_trans.
    apply effstep_plus_one. constructor.
    eexact A. 
  * econstructor; eauto.
    eapply match_stackframes_sub; try eassumption. intros b Hb; rewrite Hb; trivial.  
    apply wt_regset_assign; auto. rewrite WTRES0; auto.
    (*CompComp adaptation: new retty clause:*)
    + clear - AGRTY. red. red in AGRTY. simpl in AGRTY.
      destruct s; simpl; trivial.
    + intros; subst. apply AGRTY.

    + destruct Lsp as [b [z [SP Lsp]]]; subst. exists b, z; rewrite Lsp; split; trivial.
  * discriminate.
Qed.

(*CcompComp: initial and final states handled diffferently
Lemma initial_states_simulation:
  forall st1, RTL_memsem.initial_state prog st1 ->
  exists st2, LTL_memsem.initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inv H.
  exploit function_ptr_translated; eauto. intros [tf [FIND TR]].
  exploit sig_function_translated; eauto. intros SIG.
  exists (LTL_memsem.Callstate nil tf (Locmap.init Vundef) m0); split.
  econstructor; eauto.
  eapply (Genv.init_mem_transf_partial TRANSF); eauto.
  rewrite symbols_preserved.
  rewrite (match_program_main TRANSF).  auto.
  congruence.
  constructor; auto.
  constructor. rewrite SIG; rewrite H3; auto.
  rewrite SIG, H3, loc_arguments_main. auto.
  red; auto.
  apply Mem.extends_refl.
  rewrite SIG, H3. constructor.
Qed.

Lemma final_states_simulation:
  forall st1 st2 r,
  match_states st1 st2 -> RTL_memsem.final_state st1 r -> LTL_memsem.final_state st2 r.
Proof.
  intros. inv H0. inv H. inv STACKS. 
  econstructor.
  unfold loc_result in RES; rewrite H in RES. simpl in RES. inv RES. auto. 
Qed.*)

Lemma subject_reduction_N:
  forall p : RTL_memsem.program,
  wt_program p ->
  forall n (st1 : RTL_memsem.state) (m1 : mem) (st2 : RTL_memsem.state) (m2 : mem),
  corestepN  RTL_memsem.RTL_mem_sem (Genv.globalenv p) n st1 m1 st2 m2 ->
  wt_state st1 m1 -> wt_state st2 m2.
Proof. intros p P n. induction n; simpl; intros.
+ inv H; trivial.
+ destruct H as [? [? [? ?]]]. eapply IHn; eauto. eapply subject_reduction; eauto.
Qed.

Lemma subject_reduction_plus:
  forall p : RTL_memsem.program,
  wt_program p ->
  forall (st1 : RTL_memsem.state) (m1 : mem) (st2 : RTL_memsem.state) (m2 : mem),
  corestep_plus RTL_memsem.RTL_mem_sem (Genv.globalenv p) st1 m1 st2 m2 ->
  wt_state st1 m1 -> wt_state st2 m2.
Proof. intros. destruct H0. eapply subject_reduction_N; eauto. Qed.

Lemma wt_prog: wt_program prog.
Proof.
  red; intros. 
  exploit list_forall2_in_left. eexact (proj1 TRANSF). eauto. 
  intros ([i' gd] & A & B & C). simpl in *; subst i'.
  inv C. destruct f; simpl in *.
- monadInv H2.  
  unfold transf_function in EQ.
  destruct (type_function f) as [env|] eqn:TF; try discriminate.
  econstructor. eapply type_function_correct; eauto.
- constructor.
Qed.

Lemma lessdef_map: forall l t n v k ty, n+(typesize ty) <= k ->
  Val.lessdef_list
     (map (fun p : rpair loc => Locmap.getpair p t) (loc_arguments_rec l k))
     (map (fun p : rpair loc => Locmap.getpair p (Locmap.set (S Outgoing n ty) v t)) (loc_arguments_rec l k)).
Proof. induction l; simpl; intros. constructor.
  destruct a; simpl.
+ constructor. rewrite Locmap.gso. apply Val.lessdef_refl. simpl. right. left. omega. simpl in IHl.
    apply (IHl t n v). omega.
+ constructor. rewrite Locmap.gso. apply Val.lessdef_refl. simpl. right. left. omega. simpl in IHl.
    apply (IHl t n v). omega.
+ constructor. apply Val.longofwords_lessdef. rewrite Locmap.gso. apply Val.lessdef_refl. simpl. right. left. omega.
               rewrite Locmap.gso. apply Val.lessdef_refl. simpl. right. left. omega.
    apply (IHl t n v). simpl. omega.
+ constructor. rewrite Locmap.gso. apply Val.lessdef_refl. simpl. right. left. omega. simpl in IHl.
    apply (IHl t n v). omega.
+ constructor. rewrite Locmap.gso. apply Val.lessdef_refl. simpl. right. left. omega. simpl in IHl.
    apply (IHl t n v). omega.
+ constructor. rewrite Locmap.gso. apply Val.lessdef_refl. simpl. right. left. omega. simpl in IHl.
    apply (IHl t n v). omega.
Qed.

Lemma setlocs_lessdef: forall vals2 sigargs n s t,  
  setlocs (regs_of_rpairs (loc_arguments_rec sigargs n)) vals2 s = Some t ->
  val_has_type_list_func vals2 sigargs = true ->
  vals_defined vals2 = true ->
  Val.lessdef_list vals2 (map (fun p : rpair loc => Locmap.getpair p t) (loc_arguments_rec sigargs n)).
Proof. induction vals2; simpl; intros; destruct sigargs; try discriminate; simpl in *.
+ constructor.
+ apply andb_true_iff in H0. destruct H0.
  destruct a; try discriminate.
  - destruct t0; simpl in *; try discriminate.
    * clear H0. remember (setlocs (regs_of_rpairs (loc_arguments_rec sigargs (n + 1))) vals2 s).
      symmetry in Heqo; destruct o; inv H.
      specialize (IHvals2 _ _ _ _ Heqo H2 H1). 
      constructor. rewrite Locmap.gss. simpl. constructor.
      eapply Val.lessdef_list_trans. eassumption. apply lessdef_map; simpl. omega.
    * clear H0. remember (setlocs (regs_of_rpairs (loc_arguments_rec sigargs (n + 1))) vals2 s).
      symmetry in Heqo; destruct o; inv H.
      specialize (IHvals2 _ _ _ _ Heqo H2 H1). 
      constructor. rewrite Locmap.gss. simpl. constructor.
      eapply Val.lessdef_list_trans. eassumption. apply lessdef_map; simpl. omega.
    * clear H0. remember (setlocs (regs_of_rpairs (loc_arguments_rec sigargs (n + 2))) vals2 s).
      symmetry in Heqo; destruct o; inv H.
      specialize (IHvals2 _ _ _ _ Heqo H2 H1). 
      constructor. rewrite Locmap.gss. simpl. constructor.
      eapply Val.lessdef_list_trans. eassumption. apply lessdef_map; simpl. omega.
  - destruct t0; try discriminate.
    * simpl in H0. clear H0. simpl in H. destruct vals2; try discriminate. simpl in *.
      remember (setlocs (regs_of_rpairs (loc_arguments_rec sigargs (n + 2))) vals2 s).
      symmetry in Heqo; destruct o; try discriminate. inv H.
      constructor.
      ++ rewrite Locmap.gss. simpl. admit. (*WRONG - mistake may be in the def of setlocs, or in the use of vargs in Builtineffects?*)
      ++ admit.
    * admit.
  - destruct t0; simpl in *; try discriminate.
    * clear H0. remember (setlocs (regs_of_rpairs (loc_arguments_rec sigargs (n + 2))) vals2 s).
      symmetry in Heqo; destruct o; inv H.
      specialize (IHvals2 _ _ _ _ Heqo H2 H1). 
      constructor. rewrite Locmap.gss. simpl. constructor.
      eapply Val.lessdef_list_trans. eassumption. apply lessdef_map; simpl. omega.
    * clear H0. remember (setlocs (regs_of_rpairs (loc_arguments_rec sigargs (n + 2))) vals2 s).
      symmetry in Heqo; destruct o; inv H.
      specialize (IHvals2 _ _ _ _ Heqo H2 H1). 
      constructor. rewrite Locmap.gss. simpl. constructor.
      eapply Val.lessdef_list_trans. eassumption. apply lessdef_map; simpl. omega.
  - destruct t0; simpl in *; try discriminate.
    * clear H0. remember (setlocs (regs_of_rpairs (loc_arguments_rec sigargs (n + 1))) vals2 s).
      symmetry in Heqo; destruct o; inv H.
      specialize (IHvals2 _ _ _ _ Heqo H2 H1). 
      constructor. rewrite Locmap.gss. simpl. constructor.
      eapply Val.lessdef_list_trans. eassumption. apply lessdef_map; simpl. omega.
    * clear H0. remember (setlocs (regs_of_rpairs (loc_arguments_rec sigargs (n + 1))) vals2 s).
      symmetry in Heqo; destruct o; inv H.
      specialize (IHvals2 _ _ _ _ Heqo H2 H1). 
      constructor. rewrite Locmap.gss. simpl. constructor.
      eapply Val.lessdef_list_trans. eassumption. apply lessdef_map; simpl. omega.
    * clear H0. remember (setlocs (regs_of_rpairs (loc_arguments_rec sigargs (n + 2))) vals2 s).
      symmetry in Heqo; destruct o; inv H.
      specialize (IHvals2 _ _ _ _ Heqo H2 H1). 
      constructor. rewrite Locmap.gss. simpl. constructor.
      eapply Val.lessdef_list_trans. eassumption. apply lessdef_map; simpl. omega.
  - destruct t0; simpl in *; try discriminate.
    * clear H0. remember (setlocs (regs_of_rpairs (loc_arguments_rec sigargs (n + 1))) vals2 s).
      symmetry in Heqo; destruct o; inv H.
      specialize (IHvals2 _ _ _ _ Heqo H2 H1). 
      constructor. rewrite Locmap.gss. simpl. constructor.
      eapply Val.lessdef_list_trans. eassumption. apply lessdef_map; simpl. omega.
    * clear H0. remember (setlocs (regs_of_rpairs (loc_arguments_rec sigargs (n + 1))) vals2 s).
      symmetry in Heqo; destruct o; inv H.
      specialize (IHvals2 _ _ _ _ Heqo H2 H1). 
      constructor. rewrite Locmap.gss. simpl. constructor.
      eapply Val.lessdef_list_trans. eassumption. apply lessdef_map; simpl. omega.
    * clear H0. remember (setlocs (regs_of_rpairs (loc_arguments_rec sigargs (n + 2))) vals2 s).
      symmetry in Heqo; destruct o; inv H.
      specialize (IHvals2 _ _ _ _ Heqo H2 H1). 
      constructor. rewrite Locmap.gss. simpl. constructor.
      eapply Val.lessdef_list_trans. eassumption. apply lessdef_map; simpl. omega.
Admitted. 

Definition SIM: Mini_simulation_ext.Mini_simulation_extend RTL_eff_sem LTL_eff_sem ge tge.
econstructor.
+ apply well_founded_ltof. 
+ split. apply senv_preserved. admit. (*genv_domain_eq*)
+ instantiate (1:= fun d c1 m1 L c2 m2 => d=c1 /\ match_states L c1 m1 c2 m2 /\
      wt_state c1 m1 /\ (forall b, L b = true -> Mem.valid_block m1 b) /\ 
      mem_respects_readonly ge m1 /\ mem_respects_readonly tge m2).
  intros. destruct H as [? [MS [WT [HL [MRSrc MRTgt]]]]]; subst.
  apply match_states_extends in MS. apply HL in H0. split; trivial.
  eapply (Mem.valid_block_extends m1); eassumption. 
+ intros. destruct H as [? [MS [WT [HL [MRSrc MRTgt]]]]]; subst.
  apply match_states_extends in MS. apply Mem.valid_block_extends; trivial. 
+ admit. (*genv stuff*)
+ (*initialCore*)
  intros. simpl in *. destruct v; inv H; simpl.
  destruct (Int.eq_dec i Int.zero); inv H7.
  remember (Genv.find_funct_ptr ge b) as q; symmetry in Heqq; destruct q; inv H6.
  destruct (function_ptr_translated _ _ Heqq) as [x [TFP TF]]; rewrite TFP. 
  destruct f; inv H7. exploit bind_inversion. apply TF. intros [tf [HTF OKx]]; inv OKx.
  rewrite <- (mem_lemmas.Forall2_Zlength H0).
  remember (val_casted.val_has_type_list_func vals1 (sig_args (RTL_memsem.fn_sig f)) &&
       val_casted.vals_defined vals1) as d. symmetry in Heqd.
  destruct d; inv H6. apply andb_true_iff in Heqd. destruct Heqd.
  destruct (zlt
      match
        match Zlength vals1 with
        | 0 => 0
        | Z.pos y' => Z.pos y'~0
        | Z.neg y' => Z.neg y'~0
        end
      with
      | 0 => 0
      | Z.pos y' => Z.pos y'~0~0
      | Z.neg y' => Z.neg y'~0~0
      end Int.max_unsigned); inv H7. simpl. simpl in H.
  specialize (sig_function_translated _ _ TF); simpl. intros HH; rewrite <- HH in *.
  erewrite val_list_lessdef_hastype; try eassumption.
  erewrite vals_lessdef_defined; try eassumption; simpl.
  remember (setlocs (regs_of_rpairs (loc_arguments (fn_sig tf))) vals2 (Locmap.init Vundef)).
  symmetry in Heqo; destruct o.
  - eexists; eexists; split. reflexivity.
    split. reflexivity.
         split. constructor; eauto. constructor. clear l H4 H5 HH.
         eapply Val.lessdef_list_trans. apply forall_lessdef_val_listless; apply H0. 
         eapply val_list_lessdef_hastype in H; eauto.
         eapply vals_lessdef_defined in H6; try eassumption. clear H0 vals1 HTF TF Heqq TFP H1 H2 H3 f m1 m2.
         simpl in *. unfold loc_arguments in *.
         remember (sig_args (fn_sig tf)) as sigargs. clear Heqsigargs. remember (Locmap.init Vundef) as s. clear Heqs.
         eapply setlocs_lessdef; eassumption.
           admit. (*TODO in initialcore clause*)
           simpl. apply val_has_type_list_func_charact. assumption.
           constructor. 
           simpl. rewrite <- HH; trivial.
          intuition. constructor. constructor. 
          destruct (Genv.find_funct_ptr_inversion prog _  Heqq) as [ID HID]. eapply wt_prog; eassumption.
     simpl in H. simpl. rewrite <- HH. rewrite <- val_has_type_list_func_charact in H.  trivial.
  - exfalso. unfold loc_arguments in Heqo. remember (sig_args (fn_sig tf)). (*clear - H0 H Heqo.
Goal forall vals1 vals2 (H :Forall2 Val.lessdef vals1 vals2) l (L:val_has_type_list_func vals1 l = true) M n,
      exists x, setlocs (regs_of_rpairs (loc_arguments_rec l n)) vals2 M = Some x.
Proof. induction vals1; simpl; intros; inv H.
+ destruct l; try discriminate. simpl. eexists; reflexivity.
+ destruct l; try discriminate. apply andb_true_iff in L. destruct L. simpl in *.
(*  specialize (IHForall2 _ H2).*)
  destruct t; inv H; simpl in *.
  -  unfold val_has_type_func in H3. destruct a; try discriminate; simpl.
     * destruct (IHvals1 _ H4 _ H0 M (n+1)) as [q Q]; rewrite Q. eexists; reflexivity.
     * destruct (IHvals1 _ H4 _ H0 M (n+1)) as [q Q]; rewrite Q. eexists; reflexivity.
     * destruct (IHvals1 _ H4 _ H0 M (n+1)) as [q Q]; rewrite Q. eexists; reflexivity.
  -  unfold val_has_type_func in H3. destruct a; try discriminate; simpl.
     * destruct (IHvals1 _ H4 _ H0 M (n+2)) as [q Q]; rewrite Q. eexists; reflexivity.
     * destruct (IHvals1 _ H4 _ H0 M (n+2)) as [q Q]; rewrite Q. eexists; reflexivity.
  -  unfold val_has_type_func in H3. destruct a; try discriminate; simpl. 
     * clear H3. destruct l'.
       ++ inv H4. simpl in *. destruct l; try discriminate.
          assert (Forall2 Val.lessdef nil nil) by constructor.
          specialize (IHvals1 _ H nil (eq_refl _)). simpl in *.  _ H0 M (n+2)) as [q Q]. rewrite Q. eexists; reflexivity.invForall2 Val.lessdef nil vals2  destruct (IHvals1 _ H4 _ H0 M (n+2)) as [q Q]; rewrite Q. eexists; reflexivity.
     * destruct (IHvals1 _ H4 _ H0 M (n+1)) as [q Q]; rewrite Q. eexists; reflexivity.
     * destruct (IHvals1 _ H4 _ H0 M (n+1)) as [q Q]; rewrite Q. eexists; reflexivity.
     * destruct (IHvals1 _ H4 _ H0 M (n+1)) as [q Q]; rewrite Q. eexists; reflexivity.
  
     * destruct (IHForall2 _ H2 M (n+1)) as [q Q]; rewrite Q. eexists; reflexivity.
     * destruct (IHForall2 _ H2 M (n+1)) as [q Q]; rewrite Q. eexists; reflexivity.
  - unfold val_has_type_func in H4. destruct x; try discriminate; simpl.
     * destruct (IHForall2 M (n+2)) as [q Q]; rewrite Q. eexists; reflexivity.
     * destruct (IHForall2 M (n+2)) as [q Q]; rewrite Q. eexists; reflexivity.
  - unfold val_has_type_func in H4. destruct x; try discriminate; simpl.
     * destruct (IHForall2 M (n+2)) as [q Q]; rewrite Q. eexists; reflexivity.
     * destruct (IHForall2 M (n+2)) as [q Q]; rewrite Q. eexists; reflexivity.
     * destruct (IHForall2 M (n+1)) as [q Q]; rewrite Q. eexists; reflexivity.
     * destruct (IHForall2 M (n+1)) as [q Q]; rewrite Q. eexists; reflexivity.
  -  destruct (IHForall2 M (n+1)) as [q Q]; rewrite Q. eexists; reflexivity.*) admit. (*property of setlocs*)       
+ (*diagram*)
  intros. destruct H0 as [? [MS [HL [MRSrc MRTgt]]]]; subst.
  exploit core_diagram; eauto. intros [st2' [m2' [U' [STEP' [MS' HU']]]]].
  exists st2', m2', st1', (fun b : block => L b || freshblock m2 m2' b); intuition.
  { apply match_states_extends in MS'. 
    apply match_states_extends in MS. clear - MS MS'.
    erewrite extends_extends_freshblock; eauto. }
  eapply subject_reduction; eauto. apply wt_prog. eapply rtl_effax1. apply H.
  apply orb_true_iff in H2. destruct H2. eapply effstep_fwd; eauto.
  apply match_states_extends in MS'. apply freshblockProp_char in H2. destruct H2. eapply (Mem.valid_block_extends m1'); eassumption.
  - exploit mem_step_readonly. eapply effstep_mem. apply H.
    intros [Fwd RD]. eapply mem_respects_readonly_fwd; eauto.
  - exploit mem_step_readonly. eapply effstep_plus_mem. apply STEP'.
    intros [Fwd RD]. eapply mem_respects_readonly_fwd; eauto.
  - exists U'; split; trivial. left; trivial.
+ (*halted*)
  intros. destruct st1; inv H0. destruct stack; inv H2. destruct H as [? [MS [WT [HL [MRRsrc MRRTgt]]]]]; subst.
  inv MS. inv STACKS. inv WT.
  specialize (AGNIL (eq_refl _)). subst retty.
  unfold agree_retty in AGRTY. simpl in AGRTY. inv H1.
  eexists; split. eassumption. simpl. intuition.
+ (*atExternal*)
  intros. destruct st1; inv H0. destruct f; inv H2.
  destruct H as [? [MS [HL [MRSrc MRTgt]]]]; subst. inv MS.
  inv FUN. intuition. simpl.
  destruct (BuiltinEffects.observableEF_dec e0); inv H1. 
  eexists; split. apply mem_lemmas.val_listless_forall_lessdef; eassumption.
  reflexivity.
+ (*afterExternal*)
  intros. destruct st1; inv AtExtSrc. destruct f; inv H0.
  destruct MatchMu as [? [MS [WT [HL [MRSrc MRTgt]]]]]; subst. inv MS.
  inv FUN. inv WT. simpl in *.
  destruct (BuiltinEffects.observableEF_dec e0); inv H1. inv AtExtTgt.
  (*
  ++ specialize (AGNIL (eq_refl _)). subst retty.
     inv STACKS. unfold agree_retty in AGRTY. simpl in AGRTY. clear AGRTY. *)
     eexists; eexists; eexists. split. reflexivity. split. reflexivity.
     split. reflexivity.  
     split. { econstructor; eauto.
              + unfold proj_sig_res in *. unfold loc_result.
                remember (sig_res (ef_sig e)) as sr; destruct sr; simpl.
                - destruct t; try rewrite Locmap.gss_reg; trivial. simpl. 
                  rewrite Locmap.gss_reg. rewrite Locmap.gso. rewrite Locmap.gss_reg, val_longofwords_eq; trivial.
                  simpl. discriminate.
                - rewrite Locmap.gss; trivial.
              + red; intros. rewrite (AG _ H). destruct l; simpl in *.
                destruct r; inv H; simpl;
                unfold loc_result; destruct (sig_res (ef_sig e)); try destruct t; simpl; reflexivity.
                unfold loc_result; destruct (sig_res (ef_sig e)); try destruct t; simpl; reflexivity.
              + red. red in AGRTY. destruct stack; simpl in *; trivial. 
                destruct s; simpl in *; trivial. clear AGNIL. inv H3. inv STACKS. destruct Lsp as [bsp [z [ Lsp]]]. subst.
                rewrite <- H11 in *.
                destruct stack; simpl in *; trivial.
                - rewrite AGRTY. inv STACKS0. inv H12.  unfold transf_function in FUN.
                  remember (type_function f). destruct r; try discriminate.  
                  remember (regalloc f). destruct r0; try discriminate. apply bind_inversion in FUN. destruct FUN as [? [? ?]]. inv H1. simpl in *.
                  admit. (*e and f got confused - maybe add retty in rtltyping.wt_stackframes_nil after all??*) 
                - inv STACKS0. admit. }
     split. econstructor. eassumption. apply HasTy1.  
     split. intros. apply FwdSrc; eauto.
     split; eapply mem_respects_readonly_forward'; try eassumption. 
Admitted.
  
(*
Theorem transf_program_correct:
  forward_simulation (RTL_memsem.semantics prog) (LTL_memsem.semantics tprog).
Proof.
  set (ms := fun s s' => wt_state s /\ match_states s s').
  eapply forward_simulation_plus with (match_states := ms).
- apply senv_preserved.
- intros. exploit initial_states_simulation; eauto. intros [st2 [A B]].
  exists st2; split; auto. split; auto.
  apply wt_initial_state with (p := prog); auto. exact wt_prog.
- intros. destruct H. eapply final_states_simulation; eauto.
- intros. destruct H0.
  exploit step_simulation; eauto. intros [s2' [A B]].
  exists s2'; split. exact A. split.
  eapply subject_reduction; eauto. eexact wt_prog. eexact H.
  auto.
Qed.
*)
End PRESERVATION.
