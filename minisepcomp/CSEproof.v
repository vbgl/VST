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

(** Correctness proof for common subexpression elimination. *)

Require Import Coqlib Maps Errors Integers Floats minisepcomp.Lattice minisepcomp.Kildall.
Require Import AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import minisepcomp.Op minisepcomp.Registers minisepcomp.RTL_memsem.
Require Import minisepcomp.ValueDomain minisepcomp.ValueAOp minisepcomp.ValueAnalysis.
Require Import minisepcomp.CSEdomain minisepcomp.CombineOp minisepcomp.CombineOpproof minisepcomp.CSE.

Require Import minisepcomp.val_casted.

Definition match_prog (prog tprog: RTL_memsem.program) :=
  match_program (fun cu f tf => transf_fundef (romem_for cu) f = OK tf) eq prog tprog.

Lemma transf_program_match:
  forall prog tprog, transf_program prog = OK tprog -> match_prog prog tprog.
Proof.
  intros. eapply match_transform_partial_program_contextual; eauto.
Qed.

(** * Soundness of operations over value numberings *)

Remark wf_equation_incr:
  forall next1 next2 e,
  wf_equation next1 e -> Ple next1 next2 -> wf_equation next2 e.
Proof.
  unfold wf_equation; intros; destruct e. destruct H. split.
  apply Plt_le_trans with next1; auto.
  red; intros. apply Plt_le_trans with next1; auto. apply H1; auto.
Qed.

(** Extensionality with respect to valuations. *)

Definition valu_agree (valu1 valu2: valuation) (upto: valnum) :=
  forall v, Plt v upto -> valu2 v = valu1 v.

Section EXTEN.

Variable valu1: valuation.
Variable upto: valnum.
Variable valu2: valuation.
Hypothesis AGREE: valu_agree valu1 valu2 upto.
Variable ge: genv.
Variable sp: val.
Variable rs: regset.
Variable m: mem.

Lemma valnums_val_exten:
  forall vl,
  (forall v, In v vl -> Plt v upto) ->
  map valu2 vl = map valu1 vl.
Proof.
  intros. apply list_map_exten. intros. symmetry. auto.
Qed.

Lemma rhs_eval_to_exten:
  forall r v,
  rhs_eval_to valu1 ge sp m r v ->
  (forall v, In v (valnums_rhs r) -> Plt v upto) ->
  rhs_eval_to valu2 ge sp m r v.
Proof.
  intros. inv H; simpl in *.
- constructor. rewrite valnums_val_exten by assumption. auto.
- econstructor; eauto. rewrite valnums_val_exten by assumption. auto.
Qed.

Lemma equation_holds_exten:
  forall e,
  equation_holds valu1 ge sp m e ->
  wf_equation upto e ->
  equation_holds valu2 ge sp m e.
Proof.
  intros. destruct e. destruct H0. inv H.
- constructor. rewrite AGREE by auto. apply rhs_eval_to_exten; auto.
- econstructor. apply rhs_eval_to_exten; eauto. rewrite AGREE by auto. auto.
Qed.

Lemma numbering_holds_exten:
  forall n,
  numbering_holds valu1 ge sp rs m n ->
  Ple n.(num_next) upto ->
  numbering_holds valu2 ge sp rs m n.
Proof.
  intros. destruct H. constructor; intros.
- auto.
- apply equation_holds_exten. auto.
  eapply wf_equation_incr; eauto with cse.
- rewrite AGREE. eauto. eapply Plt_le_trans; eauto. eapply wf_num_reg; eauto.
Qed.

End EXTEN.

Ltac splitall := repeat (match goal with |- _ /\ _ => split end).

Lemma valnum_reg_holds:
  forall valu1 ge sp rs m n r n' v,
  numbering_holds valu1 ge sp rs m n ->
  valnum_reg n r = (n', v) ->
  exists valu2,
     numbering_holds valu2 ge sp rs m n'
  /\ rs#r = valu2 v
  /\ valu_agree valu1 valu2 n.(num_next)
  /\ Plt v n'.(num_next)
  /\ Ple n.(num_next) n'.(num_next).
Proof.
  unfold valnum_reg; intros.
  destruct (num_reg n)!r as [v'|] eqn:NR.
- inv H0. exists valu1; splitall.
  + auto.
  + eauto with cse.
  + red; auto.
  + eauto with cse.
  + apply Ple_refl.
- inv H0; simpl.
  set (valu2 := fun vn => if peq vn n.(num_next) then rs#r else valu1 vn).
  assert (AG: valu_agree valu1 valu2 n.(num_next)).
  { red; intros. unfold valu2. apply peq_false. apply Plt_ne; auto. }
  exists valu2; splitall.
+ constructor; simpl; intros.
* constructor; simpl; intros.
  apply wf_equation_incr with (num_next n). eauto with cse. xomega.
  rewrite PTree.gsspec in H0. destruct (peq r0 r).
  inv H0; xomega.
  apply Plt_trans_succ; eauto with cse.
  rewrite PMap.gsspec in H0. destruct (peq v (num_next n)).
  replace r0 with r by (simpl in H0; intuition). rewrite PTree.gss. subst; auto.
  exploit wf_num_val; eauto with cse. intro.
  rewrite PTree.gso by congruence. auto.
* eapply equation_holds_exten; eauto with cse.
* unfold valu2. rewrite PTree.gsspec in H0. destruct (peq r0 r).
  inv H0. rewrite peq_true; auto.
  rewrite peq_false. eauto with cse. apply Plt_ne; eauto with cse.
+ unfold valu2. rewrite peq_true; auto.
+ auto.
+ xomega.
+ xomega.
Qed.

Lemma valnum_regs_holds:
  forall rl valu1 ge sp rs m n n' vl,
  numbering_holds valu1 ge sp rs m n ->
  valnum_regs n rl = (n', vl) ->
  exists valu2,
     numbering_holds valu2 ge sp rs m n'
  /\ rs##rl = map valu2 vl
  /\ valu_agree valu1 valu2 n.(num_next)
  /\ (forall v, In v vl -> Plt v n'.(num_next))
  /\ Ple n.(num_next) n'.(num_next).
Proof.
  induction rl; simpl; intros.
- inv H0. exists valu1; splitall; auto. red; auto. simpl; tauto. xomega.
- destruct (valnum_reg n a) as [n1 v1] eqn:V1.
  destruct (valnum_regs n1 rl) as [n2 vs] eqn:V2.
  inv H0.
  exploit valnum_reg_holds; eauto.
  intros (valu2 & A & B & C & D & E).
  exploit (IHrl valu2); eauto.
  intros (valu3 & P & Q & R & S & T).
  exists valu3; splitall.
  + auto.
  + simpl; f_equal; auto. rewrite R; auto.
  + red; intros. transitivity (valu2 v); auto. apply R. xomega.
  + simpl; intros. destruct H0; auto. subst v1; xomega.
  + xomega.
Qed.

Lemma find_valnum_rhs_charact:
  forall rh v eqs,
  find_valnum_rhs rh eqs = Some v -> In (Eq v true rh) eqs.
Proof.
  induction eqs; simpl; intros.
- inv H.
- destruct a. destruct (strict && eq_rhs rh r) eqn:T.
  + InvBooleans. inv H. left; auto.
  + right; eauto.
Qed.

Lemma find_valnum_rhs'_charact:
  forall rh v eqs,
  find_valnum_rhs' rh eqs = Some v -> exists strict, In (Eq v strict rh) eqs.
Proof.
  induction eqs; simpl; intros.
- inv H.
- destruct a. destruct (eq_rhs rh r) eqn:T.
  + inv H. exists strict; auto.
  + exploit IHeqs; eauto. intros [s IN]. exists s; auto.
Qed.

Lemma find_valnum_num_charact:
  forall v r eqs, find_valnum_num v eqs = Some r -> In (Eq v true r) eqs.
Proof.
  induction eqs; simpl; intros.
- inv H.
- destruct a. destruct (strict && peq v v0) eqn:T.
  + InvBooleans. inv H. auto.
  + eauto.
Qed.

Lemma reg_valnum_sound:
  forall n v r valu ge sp rs m,
  reg_valnum n v = Some r ->
  numbering_holds valu ge sp rs m n ->
  rs#r = valu v.
Proof.
  unfold reg_valnum; intros. destruct (num_val n)#v as [ | r1 rl] eqn:E; inv H.
  eapply num_holds_reg; eauto. eapply wf_num_val; eauto with cse.
  rewrite E; auto with coqlib.
Qed.

Lemma regs_valnums_sound:
  forall n valu ge sp rs m,
  numbering_holds valu ge sp rs m n ->
  forall vl rl,
  regs_valnums n vl = Some rl ->
  rs##rl = map valu vl.
Proof.
  induction vl; simpl; intros.
- inv H0; auto.
- destruct (reg_valnum n a) as [r1|] eqn:RV1; try discriminate.
  destruct (regs_valnums n vl) as [rl1|] eqn:RVL; inv H0.
  simpl; f_equal. eapply reg_valnum_sound; eauto. eauto.
Qed.

Lemma find_rhs_sound:
  forall n rh r valu ge sp rs m,
  find_rhs n rh = Some r ->
  numbering_holds valu ge sp rs m n ->
  exists v, rhs_eval_to valu ge sp m rh v /\ Val.lessdef v rs#r.
Proof.
  unfold find_rhs; intros. destruct (find_valnum_rhs' rh (num_eqs n)) as [vres|] eqn:E; try discriminate.
  exploit find_valnum_rhs'_charact; eauto. intros [strict IN].
  erewrite reg_valnum_sound by eauto.
  exploit num_holds_eq; eauto. intros EH. inv EH.
- exists (valu vres); auto.
- exists v; auto.
Qed.

Remark in_remove:
  forall (A: Type) (eq: forall (x y: A), {x=y}+{x<>y}) x y l,
  In y (List.remove eq x l) <-> x <> y /\ In y l.
Proof.
  induction l; simpl.
  tauto.
  destruct (eq x a).
  subst a. rewrite IHl. tauto.
  simpl. rewrite IHl. intuition congruence.
Qed.

Lemma forget_reg_charact:
  forall n rd r v,
  wf_numbering n ->
  In r (PMap.get v (forget_reg n rd)) -> r <> rd /\ In r (PMap.get v n.(num_val)).
Proof.
  unfold forget_reg; intros.
  destruct (PTree.get rd n.(num_reg)) as [vd|] eqn:GET.
- rewrite PMap.gsspec in H0. destruct (peq v vd).
  + subst v. rewrite in_remove in H0. intuition.
  + split; auto. exploit wf_num_val; eauto. congruence.
- split; auto. exploit wf_num_val; eauto. congruence.
Qed.

Lemma update_reg_charact:
  forall n rd vd r v,
  wf_numbering n ->
  In r (PMap.get v (update_reg n rd vd)) ->
  PTree.get r (PTree.set rd vd n.(num_reg)) = Some v.
Proof.
  unfold update_reg; intros.
  rewrite PMap.gsspec in H0.
  destruct (peq v vd).
- subst v. destruct H0.
+ subst r. apply PTree.gss.
+ exploit forget_reg_charact; eauto. intros [A B].
  rewrite PTree.gso by auto. eapply wf_num_val; eauto.
- exploit forget_reg_charact; eauto. intros [A B].
  rewrite PTree.gso by auto. eapply wf_num_val; eauto.
Qed.

Lemma rhs_eval_to_inj:
  forall valu ge sp m rh v1 v2,
  rhs_eval_to valu ge sp m rh v1 -> rhs_eval_to valu ge sp m rh v2 -> v1 = v2.
Proof.
  intros. inv H; inv H0; congruence.
Qed.

Lemma add_rhs_holds:
  forall valu1 ge sp rs m n rd rh rs',
  numbering_holds valu1 ge sp rs m n ->
  rhs_eval_to valu1 ge sp m rh (rs'#rd) ->
  wf_rhs n.(num_next) rh ->
  (forall r, r <> rd -> rs'#r = rs#r) ->
  exists valu2, numbering_holds valu2 ge sp rs' m (add_rhs n rd rh).
Proof.
  unfold add_rhs; intros.
  destruct (find_valnum_rhs rh n.(num_eqs)) as [vres|] eqn:FIND.

- (* A value number exists already *)
  exploit find_valnum_rhs_charact; eauto. intros IN.
  exploit wf_num_eqs; eauto with cse. intros [A B].
  exploit num_holds_eq; eauto. intros EH. inv EH.
  assert (rs'#rd = valu1 vres) by (eapply rhs_eval_to_inj; eauto).
  exists valu1; constructor; simpl; intros.
+ constructor; simpl; intros.
  * eauto with cse.
  * rewrite PTree.gsspec in H5. destruct (peq r rd).
    inv H5. auto.
    eauto with cse.
  * eapply update_reg_charact; eauto with cse.
+ eauto with cse.
+ rewrite PTree.gsspec in H5. destruct (peq r rd).
  congruence.
  rewrite H2 by auto. eauto with cse.

- (* Assigning a new value number *)
  set (valu2 := fun v => if peq v n.(num_next) then rs'#rd else valu1 v).
  assert (AG: valu_agree valu1 valu2 n.(num_next)).
  { red; intros. unfold valu2. apply peq_false. apply Plt_ne; auto. }
  exists valu2; constructor; simpl; intros.
+ constructor; simpl; intros.
  * destruct H3. inv H3. simpl; split. xomega.
    red; intros. apply Plt_trans_succ; eauto.
    apply wf_equation_incr with (num_next n). eauto with cse. xomega.
  * rewrite PTree.gsspec in H3. destruct (peq r rd).
    inv H3. xomega.
    apply Plt_trans_succ; eauto with cse.
  * apply update_reg_charact; eauto with cse.
+ destruct H3. inv H3.
  constructor. unfold valu2 at 2; rewrite peq_true.
  eapply rhs_eval_to_exten; eauto.
  eapply equation_holds_exten; eauto with cse.
+ rewrite PTree.gsspec in H3. unfold valu2. destruct (peq r rd).
  inv H3. rewrite peq_true; auto.
  rewrite peq_false. rewrite H2 by auto. eauto with cse.
  apply Plt_ne; eauto with cse.
Qed.

Lemma add_op_holds:
  forall valu1 ge sp rs m n op (args: list reg) v dst,
  numbering_holds valu1 ge sp rs m n ->
  eval_operation ge sp op rs##args m = Some v ->
  exists valu2, numbering_holds valu2 ge sp (rs#dst <- v) m (add_op n dst op args).
Proof.
  unfold add_op; intros.
  destruct (is_move_operation op args) as [src|] eqn:ISMOVE.
- (* special case for moves *)
  exploit is_move_operation_correct; eauto. intros [A B]; subst op args.
  simpl in H0. inv H0.
  destruct (valnum_reg n src) as [n1 vsrc] eqn:VN.
  exploit valnum_reg_holds; eauto.
  intros (valu2 & A & B & C & D & E).
  exists valu2; constructor; simpl; intros.
+ constructor; simpl; intros; eauto with cse.
  * rewrite PTree.gsspec in H0. destruct (peq r dst).
    inv H0. auto.
    eauto with cse.
  * eapply update_reg_charact; eauto with cse.
+ eauto with cse.
+ rewrite PTree.gsspec in H0. rewrite Regmap.gsspec.
  destruct (peq r dst). congruence. eauto with cse.

- (* general case *)
  destruct (valnum_regs n args) as [n1 vl] eqn:VN.
  exploit valnum_regs_holds; eauto.
  intros (valu2 & A & B & C & D & E).
  eapply add_rhs_holds; eauto.
+ constructor. rewrite Regmap.gss. congruence.
+ intros. apply Regmap.gso; auto.
Qed.

Lemma add_load_holds:
  forall valu1 ge sp rs m n addr (args: list reg) a chunk v dst,
  numbering_holds valu1 ge sp rs m n ->
  eval_addressing ge sp addr rs##args = Some a ->
  Mem.loadv chunk m a = Some v ->
  exists valu2, numbering_holds valu2 ge sp (rs#dst <- v) m (add_load n dst chunk addr args).
Proof.
  unfold add_load; intros.
  destruct (valnum_regs n args) as [n1 vl] eqn:VN.
  exploit valnum_regs_holds; eauto.
  intros (valu2 & A & B & C & D & E).
  eapply add_rhs_holds; eauto.
+ econstructor. rewrite <- B; eauto. rewrite Regmap.gss; auto.
+ intros. apply Regmap.gso; auto.
Qed.

Lemma set_unknown_holds:
  forall valu ge sp rs m n r v,
  numbering_holds valu ge sp rs m n ->
  numbering_holds valu ge sp (rs#r <- v) m (set_unknown n r).
Proof.
  intros; constructor; simpl; intros.
- constructor; simpl; intros.
  + eauto with cse.
  + rewrite PTree.grspec in H0. destruct (PTree.elt_eq r0 r).
    discriminate.
    eauto with cse.
  + exploit forget_reg_charact; eauto with cse. intros [A B].
    rewrite PTree.gro; eauto with cse.
- eauto with cse.
- rewrite PTree.grspec in H0. destruct (PTree.elt_eq r0 r).
  discriminate.
  rewrite Regmap.gso; eauto with cse.
Qed.

Lemma set_res_unknown_holds:
  forall valu ge sp rs m n r v,
  numbering_holds valu ge sp rs m n ->
  numbering_holds valu ge sp (regmap_setres r v rs) m (set_res_unknown n r).
Proof.
  intros. destruct r; simpl; auto. apply set_unknown_holds; auto.
Qed.

Lemma kill_eqs_charact:
  forall pred l strict r eqs,
  In (Eq l strict r) (kill_eqs pred eqs) ->
  pred r = false /\ In (Eq l strict r) eqs.
Proof.
  induction eqs; simpl; intros.
- tauto.
- destruct a. destruct (pred r0) eqn:PRED.
  tauto.
  inv H. inv H0. auto. tauto.
Qed.

Lemma kill_equations_hold:
  forall valu ge sp rs m n pred m',
  numbering_holds valu ge sp rs m n ->
  (forall r v,
      pred r = false ->
      rhs_eval_to valu ge sp m r v ->
      rhs_eval_to valu ge sp m' r v) ->
  numbering_holds valu ge sp rs m' (kill_equations pred n).
Proof.
  intros; constructor; simpl; intros.
- constructor; simpl; intros; eauto with cse.
  destruct e. exploit kill_eqs_charact; eauto. intros [A B]. eauto with cse.
- destruct eq. exploit kill_eqs_charact; eauto. intros [A B].
  exploit num_holds_eq; eauto. intro EH; inv EH; econstructor; eauto.
- eauto with cse.
Qed.

Lemma kill_all_loads_hold:
  forall valu ge sp rs m n m',
  numbering_holds valu ge sp rs m n ->
  numbering_holds valu ge sp rs m' (kill_all_loads n).
Proof.
  intros. eapply kill_equations_hold; eauto.
  unfold filter_loads; intros. inv H1.
  constructor. rewrite <- H2. apply op_depends_on_memory_correct; auto.
  discriminate.
Qed.

Lemma kill_loads_after_store_holds:
  forall valu ge sp rs m n addr args a chunk v m' bc approx ae am,
  numbering_holds valu ge (Vptr sp Int.zero) rs m n ->
  eval_addressing ge (Vptr sp Int.zero) addr rs##args = Some a ->
  Mem.storev chunk m a v = Some m' ->
  genv_match bc ge ->
  bc sp = BCstack ->
  ematch bc rs ae ->
  approx = VA.State ae am ->
  numbering_holds valu ge (Vptr sp Int.zero) rs m'
                           (kill_loads_after_store approx n chunk addr args).
Proof.
  intros. apply kill_equations_hold with m; auto.
  intros. unfold filter_after_store in H6; inv H7.
- constructor. rewrite <- H8. apply op_depends_on_memory_correct; auto.
- destruct (regs_valnums n vl) as [rl|] eqn:RV; try discriminate.
  econstructor; eauto. rewrite <- H9.
  destruct a; simpl in H1; try discriminate.
  destruct a0; simpl in H9; try discriminate.
  simpl.
  rewrite negb_false_iff in H6. unfold aaddressing in H6.
  eapply Mem.load_store_other. eauto.
  eapply pdisjoint_sound. eauto.
  apply match_aptr_of_aval. eapply eval_static_addressing_sound; eauto.
  erewrite <- regs_valnums_sound by eauto. eauto with va.
  apply match_aptr_of_aval. eapply eval_static_addressing_sound; eauto with va.
Qed.

Lemma store_normalized_range_sound:
  forall bc chunk v,
  vmatch bc v (store_normalized_range chunk) ->
  Val.lessdef (Val.load_result chunk v) v.
Proof.
  intros. destruct chunk; simpl in *; destruct v; auto.
- inv H. rewrite is_sgn_sign_ext in H4 by omega. rewrite H4; auto.
- inv H. rewrite is_uns_zero_ext in H4 by omega. rewrite H4; auto.
- inv H. rewrite is_sgn_sign_ext in H4 by omega. rewrite H4; auto.
- inv H. rewrite is_uns_zero_ext in H4 by omega. rewrite H4; auto.
Qed.

Lemma add_store_result_hold:
  forall valu1 ge sp rs m' n addr args a chunk m src bc ae approx am,
  numbering_holds valu1 ge sp rs m' n ->
  eval_addressing ge sp addr rs##args = Some a ->
  Mem.storev chunk m a rs#src = Some m' ->
  ematch bc rs ae ->
  approx = VA.State ae am ->
  exists valu2, numbering_holds valu2 ge sp rs m' (add_store_result approx n chunk addr args src).
Proof.
  unfold add_store_result; intros.
  unfold avalue; rewrite H3.
  destruct (vincl (AE.get src ae) (store_normalized_range chunk)) eqn:INCL.
- destruct (valnum_reg n src) as [n1 vsrc] eqn:VR1.
  destruct (valnum_regs n1 args) as [n2 vargs] eqn:VR2.
  exploit valnum_reg_holds; eauto. intros (valu2 & A & B & C & D & E).
  exploit valnum_regs_holds; eauto. intros (valu3 & P & Q & R & S & T).
  exists valu3. constructor; simpl; intros.
+ constructor; simpl; intros; eauto with cse.
  destruct H4; eauto with cse. subst e. split.
  eapply Plt_le_trans; eauto.
  red; simpl; intros. auto.
+ destruct H4; eauto with cse. subst eq. apply eq_holds_lessdef with (Val.load_result chunk rs#src).
  apply load_eval_to with a. rewrite <- Q; auto.
  destruct a; try discriminate. simpl. eapply Mem.load_store_same; eauto.
  rewrite B. rewrite R by auto. apply store_normalized_range_sound with bc.
  rewrite <- B. eapply vmatch_ge. apply vincl_ge; eauto. apply H2.
+ eauto with cse.

- exists valu1; auto.
Qed.

Lemma kill_loads_after_storebytes_holds:
  forall valu ge sp rs m n dst b ofs bytes m' bc approx ae am sz,
  numbering_holds valu ge (Vptr sp Int.zero) rs m n ->
  pmatch bc b ofs dst ->
  Mem.storebytes m b (Int.unsigned ofs) bytes = Some m' ->
  genv_match bc ge ->
  bc sp = BCstack ->
  ematch bc rs ae ->
  approx = VA.State ae am ->
  length bytes = nat_of_Z sz -> sz >= 0 ->
  numbering_holds valu ge (Vptr sp Int.zero) rs m'
                           (kill_loads_after_storebytes approx n dst sz).
Proof.
  intros. apply kill_equations_hold with m; auto.
  intros. unfold filter_after_store in H8; inv H9.
- constructor. rewrite <- H10. apply op_depends_on_memory_correct; auto.
- destruct (regs_valnums n vl) as [rl|] eqn:RV; try discriminate.
  econstructor; eauto. rewrite <- H11.
  destruct a; simpl in H10; try discriminate.
  simpl.
  rewrite negb_false_iff in H8.
  eapply Mem.load_storebytes_other. eauto.
  rewrite H6. rewrite nat_of_Z_eq by auto.
  eapply pdisjoint_sound. eauto.
  unfold aaddressing. apply match_aptr_of_aval. eapply eval_static_addressing_sound; eauto.
  erewrite <- regs_valnums_sound by eauto. eauto with va.
  auto.
Qed.

Lemma load_memcpy:
  forall m b1 ofs1 sz bytes b2 ofs2 m' chunk i v,
  Mem.loadbytes m b1 ofs1 sz = Some bytes ->
  Mem.storebytes m b2 ofs2 bytes = Some m' ->
  Mem.load chunk m b1 i = Some v ->
  ofs1 <= i -> i + size_chunk chunk <= ofs1 + sz ->
  (align_chunk chunk | ofs2 - ofs1) ->
  Mem.load chunk m' b2 (i + (ofs2 - ofs1)) = Some v.
Proof.
  intros.
  generalize (size_chunk_pos chunk); intros SPOS.
  set (n1 := i - ofs1).
  set (n2 := size_chunk chunk).
  set (n3 := sz - (n1 + n2)).
  replace sz with (n1 + (n2 + n3)) in H by (unfold n3, n2, n1; omega).
  exploit Mem.loadbytes_split; eauto.
  unfold n1; omega.
  unfold n3, n2, n1; omega.
  intros (bytes1 & bytes23 & LB1 & LB23 & EQ).
  clear H.
  exploit Mem.loadbytes_split; eauto.
  unfold n2; omega.
  unfold n3, n2, n1; omega.
  intros (bytes2 & bytes3 & LB2 & LB3 & EQ').
  subst bytes23; subst bytes.
  exploit Mem.load_loadbytes; eauto. intros (bytes2' & A & B).
  assert (bytes2' = bytes2).
  { replace (ofs1 + n1) with i in LB2 by (unfold n1; omega). unfold n2 in LB2. congruence.  }
  subst bytes2'.
  exploit Mem.storebytes_split; eauto. intros (m1 & SB1 & SB23).
  clear H0.
  exploit Mem.storebytes_split; eauto. intros (m2 & SB2 & SB3).
  clear SB23.
  assert (L1: Z.of_nat (length bytes1) = n1).
  { erewrite Mem.loadbytes_length by eauto. apply nat_of_Z_eq. unfold n1; omega. }
  assert (L2: Z.of_nat (length bytes2) = n2).
  { erewrite Mem.loadbytes_length by eauto. apply nat_of_Z_eq. unfold n2; omega. }
  rewrite L1 in *. rewrite L2 in *.
  assert (LB': Mem.loadbytes m2 b2 (ofs2 + n1) n2 = Some bytes2).
  { rewrite <- L2. eapply Mem.loadbytes_storebytes_same; eauto. }
  assert (LB'': Mem.loadbytes m' b2 (ofs2 + n1) n2 = Some bytes2).
  { rewrite <- LB'. eapply Mem.loadbytes_storebytes_other; eauto.
    unfold n2; omega.
    right; left; omega. }
  exploit Mem.load_valid_access; eauto. intros [P Q].
  rewrite B. apply Mem.loadbytes_load.
  replace (i + (ofs2 - ofs1)) with (ofs2 + n1) by (unfold n1; omega).
  exact LB''.
  apply Z.divide_add_r; auto.
Qed.

Lemma shift_memcpy_eq_wf:
  forall src sz delta e e' next,
  shift_memcpy_eq src sz delta e = Some e' ->
  wf_equation next e ->
  wf_equation next e'.
Proof with (try discriminate).
  unfold shift_memcpy_eq; intros.
  destruct e. destruct r... destruct a...
  destruct (zle src (Int.unsigned i) &&
        zle (Int.unsigned i + size_chunk m) (src + sz) &&
        zeq (delta mod align_chunk m) 0 && zle 0 (Int.unsigned i + delta) &&
        zle (Int.unsigned i + delta) Int.max_unsigned)...
  inv H. destruct H0. split. auto. red; simpl; tauto.
Qed.

Lemma shift_memcpy_eq_holds:
  forall src dst sz e e' m sp bytes m' valu ge,
  shift_memcpy_eq src sz (dst - src) e = Some e' ->
  Mem.loadbytes m sp src sz = Some bytes ->
  Mem.storebytes m sp dst bytes = Some m' ->
  equation_holds valu ge (Vptr sp Int.zero) m e ->
  equation_holds valu ge (Vptr sp Int.zero) m' e'.
Proof with (try discriminate).
  intros. set (delta := dst - src) in *. unfold shift_memcpy_eq in H.
  destruct e as [l strict rhs] eqn:E.
  destruct rhs as [op vl | chunk addr vl]...
  destruct addr...
  set (i1 := Int.unsigned i) in *. set (j := i1 + delta) in *.
  destruct (zle src i1)...
  destruct (zle (i1 + size_chunk chunk) (src + sz))...
  destruct (zeq (delta mod align_chunk chunk) 0)...
  destruct (zle 0 j)...
  destruct (zle j Int.max_unsigned)...
  simpl in H; inv H.
  assert (LD: forall v,
    Mem.loadv chunk m (Vptr sp i) = Some v ->
    Mem.loadv chunk m' (Vptr sp (Int.repr j)) = Some v).
  {
    simpl; intros. rewrite Int.unsigned_repr by omega.
    unfold j, delta. eapply load_memcpy; eauto.
    apply Zmod_divide; auto. generalize (align_chunk_pos chunk); omega.
  }
  inv H2.
+ inv H3. destruct vl... simpl in H6. rewrite Int.add_zero_l in H6. inv H6.
  apply eq_holds_strict. econstructor. simpl. rewrite Int.add_zero_l. eauto.
  apply LD; auto.
+ inv H4. destruct vl... simpl in H7. rewrite Int.add_zero_l in H7. inv H7.
  apply eq_holds_lessdef with v; auto.
  econstructor. simpl. rewrite Int.add_zero_l. eauto. apply LD; auto.
Qed.

Lemma add_memcpy_eqs_charact:
  forall e' src sz delta eqs2 eqs1,
  In e' (add_memcpy_eqs src sz delta eqs1 eqs2) ->
  In e' eqs2 \/ exists e, In e eqs1 /\ shift_memcpy_eq src sz delta e = Some e'.
Proof.
  induction eqs1; simpl; intros.
- auto.
- destruct (shift_memcpy_eq src sz delta a) as [e''|] eqn:SHIFT.
  + destruct H. subst e''. right; exists a; auto.
    destruct IHeqs1 as [A | [e [A B]]]; auto. right; exists e; auto.
  + destruct IHeqs1 as [A | [e [A B]]]; auto. right; exists e; auto.
Qed.

Lemma add_memcpy_holds:
  forall m bsrc osrc sz bytes bdst odst m' valu ge sp rs n1 n2 bc asrc adst,
  Mem.loadbytes m bsrc (Int.unsigned osrc) sz = Some bytes ->
  Mem.storebytes m bdst (Int.unsigned odst) bytes = Some m' ->
  numbering_holds valu ge (Vptr sp Int.zero) rs m n1 ->
  numbering_holds valu ge (Vptr sp Int.zero) rs m' n2 ->
  pmatch bc bsrc osrc asrc ->
  pmatch bc bdst odst adst ->
  bc sp = BCstack ->
  Ple (num_next n1) (num_next n2) ->
  numbering_holds valu ge (Vptr sp Int.zero) rs m' (add_memcpy n1 n2 asrc adst sz).
Proof.
  intros. unfold add_memcpy.
  destruct asrc; auto; destruct adst; auto.
  assert (A: forall b o i, pmatch bc b o (Stk i) -> b = sp /\ i = o).
  {
    intros. inv H7. split; auto. eapply bc_stack; eauto.
  }
  apply A in H3; destruct H3. subst bsrc ofs.
  apply A in H4; destruct H4. subst bdst ofs0.
  constructor; simpl; intros; eauto with cse.
- constructor; simpl; eauto with cse.
  intros. exploit add_memcpy_eqs_charact; eauto. intros [X | (e0 & X & Y)].
  eauto with cse.
  apply wf_equation_incr with (num_next n1); auto.
  eapply shift_memcpy_eq_wf; eauto with cse.
- exploit add_memcpy_eqs_charact; eauto. intros [X | (e0 & X & Y)].
  eauto with cse.
  eapply shift_memcpy_eq_holds; eauto with cse.
Qed.

(** Correctness of operator reduction *)

Section REDUCE.

Variable A: Type.
Variable f: (valnum -> option rhs) -> A -> list valnum -> option (A * list valnum).
Variable V: Type.
Variable ge: genv.
Variable sp: val.
Variable rs: regset.
Variable m: mem.
Variable sem: A -> list val -> option V.
Hypothesis f_sound:
  forall eqs valu op args op' args',
  (forall v rhs, eqs v = Some rhs -> rhs_eval_to valu ge sp m rhs (valu v)) ->
  f eqs op args = Some(op', args') ->
  sem op' (map valu args') = sem op (map valu args).
Variable n: numbering.
Variable valu: valnum -> val.
Hypothesis n_holds: numbering_holds valu ge sp rs m n.

Lemma reduce_rec_sound:
  forall niter op args op' rl' res,
  reduce_rec A f n niter op args = Some(op', rl') ->
  sem op (map valu args) = Some res ->
  sem op' (rs##rl') = Some res.
Proof.
  induction niter; simpl; intros.
  discriminate.
  destruct (f (fun v : valnum => find_valnum_num v (num_eqs n)) op args)
           as [[op1 args1] | ] eqn:?.
  assert (sem op1 (map valu args1) = Some res).
    rewrite <- H0. eapply f_sound; eauto.
    simpl; intros.
    exploit num_holds_eq; eauto.
    eapply find_valnum_num_charact; eauto with cse.
    intros EH; inv EH; auto.
  destruct (reduce_rec A f n niter op1 args1) as [[op2 rl2] | ] eqn:?.
  inv H. eapply IHniter; eauto.
  destruct (regs_valnums n args1) as [rl|] eqn:?.
  inv H. erewrite regs_valnums_sound; eauto.
  discriminate.
  discriminate.
Qed.

Lemma reduce_sound:
  forall op rl vl op' rl' res,
  reduce A f n op rl vl = (op', rl') ->
  map valu vl = rs##rl ->
  sem op rs##rl = Some res ->
  sem op' rs##rl' = Some res.
Proof.
  unfold reduce; intros.
  destruct (reduce_rec A f n 4%nat op vl) as [[op1 rl1] | ] eqn:?; inv H.
  eapply reduce_rec_sound; eauto. congruence.
  auto.
Qed.

End REDUCE.

(** The numberings associated to each instruction by the static analysis
  are inductively satisfiable, in the following sense: the numbering
  at the function entry point is satisfiable, and for any RTL execution
  from [pc] to [pc'], satisfiability at [pc] implies
  satisfiability at [pc']. *)

Theorem analysis_correct_1:
  forall ge sp rs m f vapprox approx pc pc' i,
  analyze f vapprox = Some approx ->
  f.(fn_code)!pc = Some i -> In pc' (successors_instr i) ->
  (exists valu, numbering_holds valu ge sp rs m (transfer f vapprox pc approx!!pc)) ->
  (exists valu, numbering_holds valu ge sp rs m approx!!pc').
Proof.
  intros.
  assert (Numbering.ge approx!!pc' (transfer f vapprox pc approx!!pc)).
    eapply Solver.fixpoint_solution; eauto.
  destruct H2 as [valu NH]. exists valu; apply H3. auto.
Qed.

Theorem analysis_correct_entry:
  forall ge sp rs m f vapprox approx,
  analyze f vapprox = Some approx ->
  exists valu, numbering_holds valu ge sp rs m approx!!(f.(fn_entrypoint)).
Proof.
  intros.
  replace (approx!!(f.(fn_entrypoint))) with Solver.L.top.
  exists (fun v => Vundef). apply empty_numbering_holds.
  symmetry. eapply Solver.fixpoint_entry; eauto.
Qed.

(** * Semantic preservation *)

Section PRESERVATION.

Variable prog: program.
Variable tprog : program.
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
  exists cu tf, Genv.find_funct tge v = Some tf /\ transf_fundef (romem_for cu) f = OK tf /\ linkorder cu prog.
Proof (Genv.find_funct_match TRANSF).

Lemma funct_ptr_translated:
  forall (b: block) (f: RTL_memsem.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists cu tf, Genv.find_funct_ptr tge b = Some tf /\ transf_fundef (romem_for cu) f = OK tf /\ linkorder cu prog.
Proof (Genv.find_funct_ptr_match TRANSF).

Lemma sig_preserved:
  forall rm f tf, transf_fundef rm f = OK tf -> funsig tf = funsig f.
Proof.
  unfold transf_fundef; intros. destruct f; monadInv H; auto.
  unfold transf_function in EQ.
  destruct (analyze f (vanalyze rm f)); try discriminate. inv EQ; auto.
Qed.

Definition transf_function' (f: function) (approxs: PMap.t numbering) : function :=
  mkfunction
    f.(fn_sig)
    f.(fn_params)
    f.(fn_stacksize)
    (transf_code approxs f.(fn_code))
    f.(fn_entrypoint).

Definition regs_lessdef (rs1 rs2: regset) : Prop :=
  forall r, Val.lessdef (rs1#r) (rs2#r).

Lemma regs_lessdef_regs:
  forall rs1 rs2, regs_lessdef rs1 rs2 ->
  forall rl, Val.lessdef_list rs1##rl rs2##rl.
Proof.
  induction rl; constructor; auto.
Qed.

Lemma set_reg_lessdef:
  forall r v1 v2 rs1 rs2,
  Val.lessdef v1 v2 -> regs_lessdef rs1 rs2 -> regs_lessdef (rs1#r <- v1) (rs2#r <- v2).
Proof.
  intros; red; intros. repeat rewrite Regmap.gsspec.
  destruct (peq r0 r); auto.
Qed.

Lemma init_regs_lessdef:
  forall rl vl1 vl2,
  Val.lessdef_list vl1 vl2 ->
  regs_lessdef (init_regs vl1 rl) (init_regs vl2 rl).
Proof.
  induction rl; simpl; intros.
  red; intros. rewrite Regmap.gi. auto.
  inv H. red; intros. rewrite Regmap.gi. auto.
  apply set_reg_lessdef; auto.
Qed.

Lemma find_function_translated:
  forall ros rs fd rs',
  find_function ge ros rs = Some fd ->
  regs_lessdef rs rs' ->
  exists cu tfd, find_function tge ros rs' = Some tfd
              /\ transf_fundef (romem_for cu) fd = OK tfd
              /\ linkorder cu prog.
Proof.
  unfold find_function; intros; destruct ros.
- specialize (H0 r). inv H0.
  apply functions_translated; auto.
  rewrite <- H2 in H; discriminate.
- rewrite symbols_preserved. destruct (Genv.find_symbol ge i).
  apply funct_ptr_translated; auto.
  discriminate.
Qed.

(** The proof of semantic preservation is a simulation argument using
  diagrams of the following form:
<<
           st1 --------------- st2
            |                   |
           t|                   |t
            |                   |
            v                   v
           st1'--------------- st2'
>>
  Left: RTL execution in the original program.  Right: RTL execution in
  the optimized program.  Precondition (top) and postcondition (bottom):
  agreement between the states, including the fact that
  the numbering at [pc] (returned by the static analysis) is satisfiable.
*)

Definition analyze (cu: program) (f: function) :=
  CSE.analyze f (vanalyze (romem_for cu) f).

Inductive match_stackframes (L: block -> bool): list stackframe -> list stackframe -> Prop :=
  | match_stackframes_nil:
      match_stackframes L nil nil
  | match_stackframes_cons:
      forall res sp pc rs f s rs' s' cu approx
           (LINK: linkorder cu prog)
           (ANALYZE: analyze cu f = Some approx)
           (SAT: forall v m, exists valu, numbering_holds valu ge sp (rs#res <- v) m approx!!pc)
           (RLD: regs_lessdef rs rs')
           (STACKS: match_stackframes L s s')
           (Lsp: exists b z, sp = Vptr b z /\ L b = true),
    match_stackframes L 
      (Stackframe res f sp pc rs :: s)
      (Stackframe res (transf_function' f approx) sp pc rs' :: s').

(*Compcomp adaptation: RTL state refactoring*)
Inductive match_states L: state -> mem -> state -> mem -> Prop :=
  | match_states_intro:
      forall s sp pc rs m s' rs' m' f cu approx
             (LINK: linkorder cu prog)
             (ANALYZE: analyze cu f = Some approx)
             (SAT: exists valu, numbering_holds valu ge sp rs m approx!!pc)
             (RLD: regs_lessdef rs rs')
             (MEXT: Mem.extends m m')
             (STACKS: match_stackframes L s s'),
      match_states L (State s f sp pc rs) m
                   (State s' (transf_function' f approx) sp pc rs') m'
  | match_states_call:
      forall s f tf args m s' args' m' cu
             (LINK: linkorder cu prog)
             (STACKS: match_stackframes L s s')
             (TFD: transf_fundef (romem_for cu) f = OK tf)
             (ARGS: Val.lessdef_list args args')
             (MEXT: Mem.extends m m'),
      match_states L (Callstate s f args) m
                   (Callstate s' tf args') m'
  | match_states_return:
      forall s s' v v' m m'
             (STACK: match_stackframes L s s')
             (RES: Val.lessdef v v')
             (MEXT: Mem.extends m m'),
      match_states L (Returnstate s v) m
                   (Returnstate s' v') m'.

Ltac TransfInstr :=
  match goal with
  | H1: (PTree.get ?pc ?c = Some ?instr), f: function, approx: PMap.t numbering |- _ =>
      cut ((transf_function' f approx).(fn_code)!pc = Some(transf_instr approx!!pc instr));
      [ simpl transf_instr
      | unfold transf_function', transf_code; simpl; rewrite PTree.gmap;
        unfold option_map; rewrite H1; reflexivity ]
  end.

(** The proof of simulation is a case analysis over the transition
  in the source code. *)

Require Import minisepcomp.mini_simulations.
Require Import minisepcomp.mini_simulations_lemmas.
Require Import msl.Axioms. (*for extensionality*)
Require Import sepcomp.mem_lemmas. 
Require Import sepcomp.semantics.
Require Import sepcomp.semantics_lemmas.
Require Import sepcomp.effect_semantics.
(*
Definition core_ord :  core_data -> core_data -> Prop:=
  fun s2 s1 => (measure s2 < measure s1)%nat.
*)

Lemma match_stackframes_sub: forall L s s' (MST: match_stackframes L s s')
  K (HLK: forall b, L b = true -> K b = true), match_stackframes K s s'.
Proof. induction 1; simpl; intros; econstructor; eauto.
destruct Lsp as [b [z [SP Lsp]]]. exists b, z; split; eauto.
Qed.

Lemma core_diagram: forall st1 m1 st1' m1' U1
  (STEP: effstep RTL_eff_sem ge U1 st1 m1 st1' m1')
  st2  m2 L (MS: match_states L st1 m1 st2 m2 /\ sound_state prog L st1 m1),
exists st2' m2' L',
  L' = (fun b : block => L b || freshblock m1 m1' b) /\
  L' = (fun b : block => L b || freshblock m2 m2' b) /\
  exists U2 : block -> Z -> bool,
     effstep RTL_eff_sem tge U2 st2 m2 st2' m2' /\
     match_states L' st1' m1' st2' m2' /\
     (forall b ofs, U2 b ofs = true -> L b = true \/ U1 b ofs = true).
Proof.
  specialize mini_locally_allocated_same; intros LOCALLOC_SAME.
  induction 1; intros; destruct MS as [MS SoundST]; inv MS; try (TransfInstr; intro C).
-  (* Inop *)
  eexists; exists m2, L. do 2 rewrite fresh_no_alloc. intuition. 
  eexists; split. eapply effexec_Inop; eauto.
  split; [| discriminate]. 
  econstructor; eauto.
    eapply analysis_correct_1; eauto. simpl; auto.
    unfold transfer; rewrite H; auto.
- (* Iop *)
  destruct (is_trivial_op op) eqn:TRIV.
+ (* unchanged *)
  exploit eval_operation_lessdef. eapply regs_lessdef_regs; eauto. eauto. eauto.
  intros [v' [A B]].
  eexists; exists m2, L. do 2 rewrite fresh_no_alloc. intuition. 
  eexists; split.
  * eapply effexec_Iop with (v := v'); eauto.
    rewrite <- A. apply eval_operation_preserved. exact symbols_preserved.
  * split; [| discriminate].
    econstructor; eauto.
    eapply analysis_correct_1; eauto. simpl; auto.
    unfold transfer; rewrite H.
    destruct SAT as [valu NH]. eapply add_op_holds; eauto.
    apply set_reg_lessdef; auto.
+ (* possibly optimized *)
  destruct (valnum_regs approx!!pc args) as [n1 vl] eqn:?.
  destruct SAT as [valu1 NH1].
  exploit valnum_regs_holds; eauto. intros (valu2 & NH2 & EQ & AG & P & Q).
  destruct (find_rhs n1 (Op op vl)) as [r|] eqn:?.
* (* replaced by move *)
  exploit find_rhs_sound; eauto. intros (v' & EV & LD).
  assert (v' = v) by (inv EV; congruence). subst v'.
  eexists; exists m2, L. do 2 rewrite fresh_no_alloc. intuition.
  eexists; split.
  -- eapply effexec_Iop; eauto. simpl; eauto.
  -- split; [| discriminate].
     econstructor; eauto.
     eapply analysis_correct_1; eauto. simpl; auto.
     unfold transfer; rewrite H.
     eapply add_op_holds; eauto.
     apply set_reg_lessdef; auto.
     eapply Val.lessdef_trans; eauto.
* (* possibly simplified *)
  destruct (reduce operation combine_op n1 op args vl) as [op' args'] eqn:?.
  assert (RES: eval_operation ge sp op' rs##args' m = Some v).
    eapply reduce_sound with (sem := fun op vl => eval_operation ge sp op vl m); eauto.
    intros; eapply combine_op_sound; eauto.
  exploit eval_operation_lessdef. eapply regs_lessdef_regs; eauto. eauto. eauto.
  intros [v' [A B]].
  eexists; exists m2, L. do 2 rewrite fresh_no_alloc. intuition.
  eexists; split.
  -- eapply effexec_Iop with (v := v'); eauto.
     rewrite <- A. apply eval_operation_preserved. exact symbols_preserved.
  -- split; [| discriminate].
     econstructor; eauto.
     eapply analysis_correct_1; eauto. simpl; auto.
     unfold transfer; rewrite H.
     eapply add_op_holds; eauto.
     apply set_reg_lessdef; auto.
- (* Iload *)
  destruct (valnum_regs approx!!pc args) as [n1 vl] eqn:?.
  destruct SAT as [valu1 NH1].
  exploit valnum_regs_holds; eauto. intros (valu2 & NH2 & EQ & AG & P & Q).
  destruct (find_rhs n1 (Load chunk addr vl)) as [r|] eqn:?.
+ (* replaced by move *)
  exploit find_rhs_sound; eauto. intros (v' & EV & LD).
  assert (v' = v) by (inv EV; congruence). subst v'.
  eexists; exists m2, L. do 2 rewrite fresh_no_alloc. intuition.
  eexists; split.
  * eapply effexec_Iop; eauto. simpl; eauto.
  * split; [| discriminate].
    econstructor; eauto.
    eapply analysis_correct_1; eauto. simpl; auto.
    unfold transfer; rewrite H.
    eapply add_load_holds; eauto.
    apply set_reg_lessdef; auto. eapply Val.lessdef_trans; eauto.
+ (* load is preserved, but addressing is possibly simplified *)
  destruct (reduce addressing combine_addr n1 addr args vl) as [addr' args'] eqn:?.
  assert (ADDR: eval_addressing ge sp addr' rs##args' = Some a).
  { eapply reduce_sound with (sem := fun addr vl => eval_addressing ge sp addr vl); eauto.
    intros; eapply combine_addr_sound; eauto. }
  exploit eval_addressing_lessdef. apply regs_lessdef_regs; eauto. eexact ADDR.
  intros [a' [A B]].
  assert (ADDR': eval_addressing tge sp addr' rs'##args' = Some a').
  { rewrite <- A. apply eval_addressing_preserved. exact symbols_preserved. }
  exploit Mem.loadv_extends; eauto.
  intros [v' [X Y]].
  eexists; exists m2, L. do 2 rewrite fresh_no_alloc. intuition.
  eexists; split.
  * eapply effexec_Iload; eauto.
  * split; [| discriminate].
    econstructor; eauto.
    eapply analysis_correct_1; eauto. simpl; auto.
    unfold transfer; rewrite H.
    eapply add_load_holds; eauto.
    apply set_reg_lessdef; auto.

- (* Istore *)
  destruct (valnum_regs approx!!pc args) as [n1 vl] eqn:?.
  destruct SAT as [valu1 NH1].
  exploit valnum_regs_holds; eauto. intros (valu2 & NH2 & EQ & AG & P & Q).
  destruct (reduce addressing combine_addr n1 addr args vl) as [addr' args'] eqn:?.
  assert (ADDR: eval_addressing ge sp addr' rs##args' = Some a).
  { eapply reduce_sound with (sem := fun addr vl => eval_addressing ge sp addr vl); eauto.
    intros; eapply combine_addr_sound; eauto. }
  exploit eval_addressing_lessdef. apply regs_lessdef_regs; eauto. eexact ADDR.
  intros [a' [A B]].
  assert (ADDR': eval_addressing tge sp addr' rs'##args' = Some a').
  { rewrite <- A. apply eval_addressing_preserved. exact symbols_preserved. }
  exploit Mem.storev_extends; eauto. intros [m'' [X Y]].
  eexists; exists m'', L.
  repeat erewrite freshblock_storev, orb_false_r_ext; try eassumption. intuition. 
  eexists; split.
  * eapply effexec_Istore; eauto.
  * split.
    -- econstructor; eauto.
       eapply analysis_correct_1; eauto. simpl; auto.
       unfold transfer; rewrite H.
       InvSoundState.
       eapply add_store_result_hold; eauto.
       eapply kill_loads_after_store_holds; eauto.
    -- eapply StoreEffect_propagate_ext; eauto.

- (* Icall *)
  exploit find_function_translated; eauto. intros (cu' & tf & FIND' & TRANSF' & LINK').
  eexists; exists m2, L. do 2 rewrite fresh_no_alloc. intuition.
  eexists; split.
  * eapply effexec_Icall; eauto.
    eapply sig_preserved; eauto.
  * split; [| discriminate].
    econstructor; eauto.
    eapply match_stackframes_cons with (cu := cu); eauto.
    intros. eapply analysis_correct_1; eauto. simpl; auto.
    unfold transfer; rewrite H.
    exists (fun _ => Vundef); apply empty_numbering_holds.
    (*compcomp: new goal L sp*)
    { inv SoundST. apply H1 in LINK; clear H1. inv LINK. eexists; eexists; split. reflexivity.
      trivial. }
    apply regs_lessdef_regs; auto.

- (* Itailcall *)
  exploit find_function_translated; eauto. intros (cu' & tf & FIND' & TRANSF' & LINK').
  exploit Mem.free_parallel_extends; eauto. intros [m'' [A B]].
  eexists; exists m''; eexists.
  erewrite freshblock_free, orb_false_r_ext; try eassumption. split. reflexivity.
  erewrite freshblock_free, orb_false_r_ext; try eassumption. split. reflexivity.
  eexists; split; [| split].
  * eapply effexec_Itailcall; eauto.
    eapply sig_preserved; eauto.
  * econstructor; eauto.
    apply regs_lessdef_regs; auto.
  * intros bb ofs EFF. apply FreeEffectD in EFF. destruct EFF as [FE1 [FE2 FE3]]; subst bb.
    left. inv SoundST. specialize (H1 _ LINK'). inv H1; trivial. 

- (* Ibuiltin *)
  rename H2 into OBS.
  exploit (@eval_builtin_args_lessdef _ ge (fun r => rs#r) (fun r => rs'#r)); eauto.
  intros (vargs' & A & B).
  exploit external_call_mem_extends; eauto.
  intros (v' & m2' & P & Q & R & S).
  eexists; exists m2'; eexists; split. reflexivity.
  split. { extensionality b. remember (L b) as q; destruct q; simpl; trivial.
           apply external_call_mem_forward in P.
           apply external_call_mem_forward in H1.
           unfold freshblock.
           destruct (valid_block_dec m b); simpl.
           + destruct (valid_block_dec m2 b); simpl.
             - do 2 rewrite andb_false_r; trivial.
             - elim n. eapply (Mem.valid_block_extends _ _ _ MEXT); trivial.
           + destruct (valid_block_dec m2 b); simpl.
             - elim n. eapply (Mem.valid_block_extends _ _ _ MEXT); trivial.
             - do 2 rewrite andb_true_r.
               destruct (valid_block_dec m' b); destruct (valid_block_dec m2' b); trivial.
               * elim n1; eapply (Mem.valid_block_extends _ _ _ R); trivial.
               * elim n1; eapply (Mem.valid_block_extends _ _ _ R); trivial. }
  eexists; split. eapply effexec_Ibuiltin; eauto.
    eapply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
    eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  split.
  * econstructor; eauto.
    eapply analysis_correct_1; eauto. simpl; auto. 
    { unfold transfer; rewrite H.
      destruct SAT as [valu NH].
      assert (CASE1: exists valu, numbering_holds valu ge sp (regmap_setres res vres rs) m' empty_numbering).
      { exists valu; apply empty_numbering_holds. }
      assert (CASE2: m' = m -> exists valu, numbering_holds valu ge sp (regmap_setres res vres rs) m' (set_res_unknown approx#pc res)).
      { intros. subst m'. exists valu. apply set_res_unknown_holds; auto. }
      assert (CASE3: exists valu, numbering_holds valu ge sp (regmap_setres res vres rs) m'
                             (set_res_unknown (kill_all_loads approx#pc) res)).
      { exists valu. apply set_res_unknown_holds. eapply kill_all_loads_hold; eauto. }
      destruct ef.
      + apply CASE1.
      + apply CASE3.
      + apply CASE1.
      + apply CASE2; inv H1; auto.
      + apply CASE3.
      + apply CASE1.
      + apply CASE1.
      + inv H0; auto. inv H3; auto. inv H4; auto.
        simpl in H1. inv H1.
        exists valu.
        apply set_res_unknown_holds.
        InvSoundState. unfold vanalyze; rewrite AN.
        assert (pmatch bc bsrc osrc (aaddr_arg (VA.State ae am) a0))
        by (eapply aaddr_arg_sound_1; eauto).
        assert (pmatch bc bdst odst (aaddr_arg (VA.State ae am) a1))
        by (eapply aaddr_arg_sound_1; eauto).
        eapply add_memcpy_holds; eauto.
        eapply kill_loads_after_storebytes_holds; eauto.
        eapply Mem.loadbytes_length; eauto.
        simpl. apply Ple_refl.
      + apply CASE2; inv H1; auto.
      + apply CASE2; inv H1; auto.
      + apply CASE1.
      + apply CASE2; inv H1; auto. }
    apply set_res_lessdef; auto.
    eapply match_stackframes_sub; try eassumption. intros bb Hbb; rewrite Hbb; trivial.

  * intros. right. eapply BuiltinEffects.BuiltinEffects_propagate_extends; eassumption.

- (* Icond *)
  destruct (valnum_regs approx!!pc args) as [n1 vl] eqn:?.
  elim SAT; intros valu1 NH1.
  exploit valnum_regs_holds; eauto. intros (valu2 & NH2 & EQ & AG & P & Q).
  destruct (reduce condition combine_cond n1 cond args vl) as [cond' args'] eqn:?.
  assert (RES: eval_condition cond' rs##args' m = Some b).
  { eapply reduce_sound with (sem := fun cond vl => eval_condition cond vl m); eauto.
    intros; eapply combine_cond_sound; eauto. }
  eexists; exists m2, L. do 2 rewrite fresh_no_alloc. intuition. 
  eexists; split. eapply effexec_Icond; eauto.
    eapply eval_condition_lessdef; eauto. apply regs_lessdef_regs; auto.
  split; [| discriminate]. 
  econstructor; eauto.
  destruct b; eapply analysis_correct_1; eauto; simpl; auto;
  unfold transfer; rewrite H; auto.

- (* Ijumptable *)
  generalize (RLD arg); rewrite H0; intro LD; inv LD.
  eexists; exists m2, L. do 2 rewrite fresh_no_alloc. intuition. 
  eexists; split. eapply effexec_Ijumptable; eauto.
  split; [| discriminate]. 
  econstructor; eauto.
  eapply analysis_correct_1; eauto. simpl. eapply list_nth_z_in; eauto.
  unfold transfer; rewrite H; auto.

- (* Ireturn *)
  exploit Mem.free_parallel_extends; eauto. intros [m'' [A B]].
  eexists; exists m'', L. 
  erewrite freshblock_free, orb_false_r_ext; try eassumption.
  erewrite freshblock_free, orb_false_r_ext; try eassumption.
  intuition.
  eexists; split. eapply effexec_Ireturn; eauto.
  split. econstructor; eauto.
         destruct or; simpl; auto.
  intros bb z EFF. apply FreeEffectD in EFF. destruct EFF as [FE1 [FE2 FE3]]; subst bb.
     inv SoundST. specialize (H1 _ LINK). inv H1. left; trivial.

- (* internal function *)
  monadInv TFD. unfold transf_function in EQ. fold (analyze cu f) in EQ.
  destruct (analyze cu f) as [approx|] eqn:?; inv EQ.
  exploit Mem.alloc_extends; eauto. apply Zle_refl. apply Zle_refl.
  intros (m'' & A & B).
  eexists; exists m''; eexists.
  erewrite freshblock_alloc; try eassumption.
  erewrite freshblock_alloc; try eassumption.
  intuition.
  eexists; split. eapply effexec_function_internal; simpl; eauto.
  split; [| discriminate]. 
  simpl. econstructor; eauto.
  eapply analysis_correct_entry; eauto.
  apply init_regs_lessdef; auto.
  eapply match_stackframes_sub; try eassumption. intros bb Hbb; rewrite Hbb; trivial.

- (* external function - now nonobservable *)
  monadInv TFD.
  (*exploit external_call_mem_extends; eauto.*)
  specialize (BuiltinEffects.EFhelpers _ OBS); intros.
  exploit (BuiltinEffects.nonobservables_mem_extends ge tge); eauto.
  intros (v' & m2' & P & Q & R & S).
  eexists; exists m2'; eexists.
  split. reflexivity.
  split. { extensionality b. remember (L b) as q; destruct q; simpl; trivial.
           apply external_call_mem_forward in P.
           apply external_call_mem_forward in H.
           unfold freshblock.
           destruct (valid_block_dec m b); simpl.
           + destruct (valid_block_dec m2 b); simpl.
             - do 2 rewrite andb_false_r; trivial.
             - elim n. eapply (Mem.valid_block_extends _ _ _ MEXT); trivial.
           + destruct (valid_block_dec m2 b); simpl.
             - elim n. eapply (Mem.valid_block_extends _ _ _ MEXT); trivial.
             - do 2 rewrite andb_true_r.
               destruct (valid_block_dec m' b); destruct (valid_block_dec m2' b); trivial.
               * elim n1; eapply (Mem.valid_block_extends _ _ _ R); trivial.
               * elim n1; eapply (Mem.valid_block_extends _ _ _ R); trivial. }
  eexists; split. eapply effexec_function_external; eauto.
          (*eapply external_call_symbols_preserved; eauto. apply senv_preserved.*)
  split. econstructor; eauto.
         eapply match_stackframes_sub; try eassumption. intros bb Hbb; rewrite Hbb; trivial.
  intros. right. eapply BuiltinEffects.BuiltinEffects_propagate_extends; eassumption.

- (* return *)
  inv STACK.
  eexists; exists m2, L. do 2 rewrite fresh_no_alloc. intuition. 
  eexists; split. eapply effexec_return; eauto.
  split; [| discriminate]. 
  econstructor; eauto.
  apply set_reg_lessdef; auto.
Qed.

Lemma matchstates_extends c1 m1 L c2 m2 (MS:match_states L c1 m1 c2 m2): Mem.extends m1 m2.
Proof. inv MS; trivial. Qed.

Definition core_data:Type := RTL_memsem.state.

(*COMCOMP adaptation: removed memory components from all 3 state constructors*)
Definition measure (st: state) : nat := 0.

Definition core_ord :  core_data -> core_data -> Prop:=
  fun s2 s1 => (measure s2 < measure s1)%nat.

Theorem external_call_match'':
  forall (g: genv) vargs m vres m' bc rm am
  (FWD : mem_forward m m')
  (GENV : genv_match bc g)
  (RO : romatch bc m rm)
  (MM : mmatch bc m am)
  (NOSTACK : bc_nostack bc)
  (j' : meminj)
  (vres' : val)
  (m'' : mem)
  (IRES : val_inject j' vres vres')
  (IMEM : Mem.inject j' m' m'')
  (UNCH1 : Mem.unchanged_on (loc_unmapped (inj_of_bc bc)) m m')
(*  (UNCH2 : Mem.unchanged_on (loc_out_of_reach (inj_of_bc bc) m) m m'')*)
  (IINCR : inject_incr (inj_of_bc bc) j') mm
  (ISEP : inject_separated (inj_of_bc bc) j' m mm)
  (ARGS : forall v : val, In v vargs -> vmatch bc v Vtop)
  (RDO : Mem.unchanged_on (loc_not_writable m) m m'),
exists bc' : block_classification,
  bc_incr bc bc' /\
  (forall b : positive, Plt b (Mem.nextblock m) -> bc' b = bc b) /\
  vmatch bc' vres Vtop /\
  genv_match bc' g /\
  romatch bc' m' rm /\
  mmatch bc' m' mtop /\
  bc_nostack bc' /\
  (forall (b : block) (ofs n : Z),
   Mem.valid_block m b -> bc b = BCinvalid -> Mem.loadbytes m' b ofs n = Mem.loadbytes m b ofs n).
Proof. intros.
  assert (JBELOW: forall b, Plt b (Mem.nextblock m) -> j' b = inj_of_bc bc b).
  {
    intros. destruct (inj_of_bc bc b) as [[b' delta] | ] eqn:EQ.
    eapply IINCR; eauto.
    destruct (j' b) as [[b'' delta'] | ] eqn:EQ'; auto. 
    exploit ISEP; eauto. tauto.
  }
  (* Part 2: constructing bc' from j' *)
  set (f := fun b => if plt b (Mem.nextblock m)
                     then bc b
                     else match j' b with None => BCinvalid | Some _ => BCother end).
  assert (F_stack: forall b1 b2, f b1 = BCstack -> f b2 = BCstack -> b1 = b2).
  {
    assert (forall b, f b = BCstack -> bc b = BCstack).
    { unfold f; intros. destruct (plt b (Mem.nextblock m)); auto. destruct (j' b); discriminate. }
    intros. apply (bc_stack bc); auto.
  }
  assert (F_glob: forall b1 b2 id, f b1 = BCglob id -> f b2 = BCglob id -> b1 = b2).
  {
    assert (forall b id, f b = BCglob id -> bc b = BCglob id).
    { unfold f; intros. destruct (plt b (Mem.nextblock m)); auto. destruct (j' b); discriminate. }
    intros. eapply (bc_glob bc); eauto.
  }
  set (bc' := BC f F_stack F_glob). unfold f in bc'.
  assert (INCR: bc_incr bc bc').
  {
    red; simpl; intros. apply pred_dec_true. eapply mmatch_below; eauto.
  }
  assert (BC'INV: forall b, bc' b <> BCinvalid -> exists b' delta, j' b = Some(b', delta)).
  {
    simpl; intros. destruct (plt b (Mem.nextblock m)).
    exists b, 0. rewrite JBELOW by auto. apply inj_of_bc_valid; auto.
    destruct (j' b) as [[b' delta] | ].
    exists b', delta; auto.
    congruence.
  }

  (* Part 3: injection wrt j' implies matching with top wrt bc' *)
  assert (PMTOP: forall b b' delta ofs, j' b = Some (b', delta) -> pmatch bc' b ofs Ptop).
  {
    intros. constructor. simpl; unfold f.
    destruct (plt b (Mem.nextblock m)).
    rewrite JBELOW in H by auto. eapply inj_of_bc_inv; eauto.
    rewrite H; congruence.
  }
  assert (VMTOP: forall v v', Val.inject j' v v' -> vmatch bc' v Vtop).
  {
    intros. inv H; constructor. eapply PMTOP; eauto.
  }
  assert (SMTOP: forall b, bc' b <> BCinvalid -> smatch bc' m' b Ptop).
  {
    intros; split; intros.
  - exploit BC'INV; eauto. intros (b' & delta & J').
    exploit Mem.load_inject. eexact IMEM. eauto. eauto. intros (v' & A & B).
    eapply VMTOP; eauto.
  - exploit BC'INV; eauto. intros (b'' & delta & J').
    exploit Mem.loadbytes_inject. eexact IMEM. eauto. eauto. intros (bytes & A & B).
    inv B. inv H3. inv H7. eapply PMTOP; eauto.
  }
  (* Conclusions *)
  exists bc'; splitall.
- (* incr *)
  exact INCR.
- (* unchanged *)
  simpl; intros. apply pred_dec_true; auto.
- (* vmatch res *)
  eapply VMTOP; eauto.
- (* genv match *)
  apply genv_match_exten with bc; auto.
  simpl; intros; split; intros.
  rewrite pred_dec_true by (eapply mmatch_below; eauto with va). auto.
  destruct (plt b (Mem.nextblock m)). auto. destruct (j' b); congruence.
  simpl; intros. rewrite pred_dec_true by (eapply mmatch_below; eauto with va). auto.
- (* romatch m' *)
  red; simpl; intros. destruct (plt b (Mem.nextblock m)).
  exploit RO; eauto. intros (R & P & Q).
  split; auto.
  split. apply bmatch_incr with bc; auto. apply bmatch_inv with m; auto.
  intros. eapply Mem.loadbytes_unchanged_on_1. apply RDO. (*Check  external_call_readonly. eapply external_call_readonly; eauto.*)
  auto. intros; red. apply Q.
  intros; red; intros; elim (Q ofs).
  apply FWD; trivial. (*eapply external_call_max_perm with (m2 := m'); eauto.*)
  destruct (j' b); congruence.
- (* mmatch top *)
  constructor; simpl; intros.
  + apply ablock_init_sound. apply SMTOP. simpl; congruence.
  + rewrite PTree.gempty in H0; discriminate.
  + apply SMTOP; auto.
  + apply SMTOP; auto.
  + red; simpl; intros. destruct (plt b (Mem.nextblock m)).
    eapply Plt_le_trans. eauto. apply forward_nextblock; trivial. (*eapply external_call_nextblock; eauto.*)
    destruct (j' b) as [[bx deltax] | ] eqn:J'.
    eapply Mem.valid_block_inject_1; eauto.
    congruence.
- (* nostack *)
  red; simpl; intros. destruct (plt b (Mem.nextblock m)).
  apply NOSTACK; auto.
  destruct (j' b); congruence.
- (* unmapped blocks are invariant *)
  intros. eapply Mem.loadbytes_unchanged_on_1; auto.
  apply UNCH1; auto. intros; red. unfold inj_of_bc; rewrite H0; auto.
Qed.

Theorem external_call_match':
  forall ef (g: genv) vargs m t vres m' bc rm am
  (RDO: Mem.unchanged_on (loc_not_writable m) m m')
  (FWD: mem_forward m m'),
  external_call ef g vargs m t vres m' ->
  genv_match bc g ->
  (forall v, In v vargs -> vmatch bc v Vtop) ->
  romatch bc m rm ->
  mmatch bc m am ->
  bc_nostack bc ->
  exists bc',
     bc_incr bc bc'
  /\ (forall b, Plt b (Mem.nextblock m) -> bc' b = bc b)
  /\ vmatch bc' vres Vtop
  /\ genv_match bc' g
  /\ romatch bc' m' rm
  /\ mmatch bc' m' mtop
  /\ bc_nostack bc'
  /\ (forall b ofs n, Mem.valid_block m b -> bc b = BCinvalid -> Mem.loadbytes m' b ofs n = Mem.loadbytes m b ofs n).
Proof.
  intros until am; intros RDO FWD EC GENV ARGS RO MM NOSTACK . 
  (* Part 1: using ec_mem_inject *)
  exploit (@external_call_mem_inject ef _ _ g vargs m t vres m' (inj_of_bc bc) m vargs).
  apply inj_of_bc_preserves_globals; auto.
  exact EC.
  eapply mmatch_inj; eauto. eapply mmatch_below; eauto.
  revert ARGS. generalize vargs.
  induction vargs0; simpl; intros; constructor.
  eapply vmatch_inj; eauto. auto.
  intros (j' & vres' & m'' & EC' & IRES & IMEM & UNCH1 & UNCH2 & IINCR & ISEP). clear EC EC'.
  eapply  external_call_match''; eassumption.
Qed.


Theorem external_call_match_extends:
  forall (g: genv) vargs m vres m' bc rm am
  (FWD : mem_forward m m')
  (GENV : genv_match bc g)
  (RO : romatch bc m rm)
  (MM : mmatch bc m am)
  (NOSTACK : bc_nostack bc)
(*  (j' : meminj)*)
  (vres' : val)
  (m'' : mem)(*
  (IRES : val_inject j' vres vres')
  (IMEM : Mem.inject j' m' m'')*)
  (IRES : Val.lessdef vres vres')
  (IMEM : Mem.extends m' m'')
  (UNCH1 : Mem.unchanged_on (loc_unmapped (inj_of_bc bc)) m m')
(*  (UNCH2 : Mem.unchanged_on (loc_out_of_reach (inj_of_bc bc) m) m m'')*)
(*  (IINCR : inject_incr (inj_of_bc bc) j') mm
  (ISEP : inject_separated (inj_of_bc bc) j' m mm)*) 
  (*(ISEP : forall b b2 delta, inj_of_bc bc b = None ->
       Mem.flat_inj (Mem.nextblock m') b = Some (b2, delta) ->
       ~ Mem.valid_block m b)*)
  (ARGS : forall v : val, In v vargs -> vmatch bc v Vtop)
  (RDO : Mem.unchanged_on (loc_not_writable m) m m'),
exists bc' : block_classification,
  bc_incr bc bc' /\
  (forall b : positive, Plt b (Mem.nextblock m) -> bc' b = bc b) /\
  vmatch bc' vres Vtop /\
  genv_match bc' g /\
  romatch bc' m' rm /\
  mmatch bc' m' mtop /\
  bc_nostack bc' /\
  (forall (b : block) (ofs n : Z),
   Mem.valid_block m b -> bc b = BCinvalid -> Mem.loadbytes m' b ofs n = Mem.loadbytes m b ofs n).
Proof. intros.
  set (j' := fun b => if plt b (Mem.nextblock m)
                      then inj_of_bc bc b else if plt b (Mem.nextblock m') then Some (b,0) else None).
  assert (JBELOW: forall b, Plt b (Mem.nextblock m) -> j' b = inj_of_bc bc b).
  {
    intros. subst j'. unfold inj_of_bc.
    destruct (plt b (Mem.nextblock m)); try contradiction. trivial. }

  (* Part 2: constructing bc' from j' *)
  set (f := fun b => if plt b (Mem.nextblock m)
                     then bc b
                     else if plt b (Mem.nextblock m') then BCother else BCinvalid).
  assert (F_stack: forall b1 b2, f b1 = BCstack -> f b2 = BCstack -> b1 = b2).
  {
    assert (forall b, f b = BCstack -> bc b = BCstack).
    { unfold f; intros. destruct (plt b (Mem.nextblock m)); auto. destruct (plt b (Mem.nextblock m')); discriminate. }
    intros. apply (bc_stack bc); auto.
  }
  assert (F_glob: forall b1 b2 id, f b1 = BCglob id -> f b2 = BCglob id -> b1 = b2).
  {
    assert (forall b id, f b = BCglob id -> bc b = BCglob id).
    { unfold f; intros. destruct (plt b (Mem.nextblock m)); auto. destruct (plt b (Mem.nextblock m')); discriminate. }
    intros. eapply (bc_glob bc); eauto.
  }
  set (bc' := BC f F_stack F_glob). unfold f in bc'.
  assert (INCR: bc_incr bc bc').
  {
    red; simpl; intros. apply pred_dec_true. eapply mmatch_below; eauto.
  }
  assert (BC'INV: forall b, bc' b <> BCinvalid -> exists b' delta, j' b = Some(b', delta)).
  {
    simpl; intros. subst j'; simpl. destruct (plt b (Mem.nextblock m)).
    exists b, 0. (*rewrite JBELOW by auto.*) apply inj_of_bc_valid; auto.
    destruct (plt b (Mem.nextblock m')); try congruence. eexists; eexists; reflexivity. 
  }

  (* Part 3: injection wrt j' implies matching with top wrt bc' *)
  assert (PMTOP: forall b b' delta ofs, j' b = Some (b', delta) -> pmatch bc' b ofs Ptop).
  {
    intros. constructor. subst j'; simpl in *; unfold f.
    destruct (plt b (Mem.nextblock m)).
(*    rewrite JBELOW in H by auto. *)eapply inj_of_bc_inv; eauto.
    destruct (plt b (Mem.nextblock m')); congruence.
  }

  assert (VMTOP: forall v v', Val.inject j' v v' -> vmatch bc' v Vtop).
  {
    intros. inv H; constructor. eapply PMTOP; eauto.
  }
  assert (VMTOP1: forall v v', Val.lessdef v v' -> 
          match v with Vptr b i => Plt b (Mem.nextblock m') | _ => True end ->
          vmatch bc' v Vtop).
  {
    intros. destruct v. constructor. constructor. constructor. constructor. constructor. constructor. inv H.        
        eapply PMTOP; eauto. instantiate (1:=0). instantiate (1:=b). subst j'. simpl.
          destruct (plt b (Mem.nextblock m)). unfold inj_of_bc. case_eq (bc b); intros HH; trivial. admit.
          destruct (plt b (Mem.nextblock m')); trivial. contradiction. 
  } 
  assert (SMTOP: forall b, bc' b <> BCinvalid -> smatch bc' m' b Ptop).
  {
    intros; split; intros.
  - exploit BC'INV; eauto. intros (b' & delta & J').
    (*exploit Mem.load_inject. eexact IMEM. eauto. eauto. intros (v' & A & B).*)
    exploit Mem.load_extends. 2: eassumption. eassumption. intros (v' & A & B).
    * specialize (VMTOP1 _ _  destruct v; try constructor.  x eapply VMTOP1; eauto. destruct v; trivial.
      clear - H0 IMEM. 
      exploit Mem.load_valid_access; eauto. intros [RP AL]. inv IMEM. clear mext_next mext_perm_inv.
      inv mext_inj. clear mi_perm mi_align.
      apply Mem.load_result in H0. 
      assert (P: Mem.perm m' b ofs Cur Readable). apply RP. specialize (size_chunk_pos chunk); omega.
      specialize (mi_memval b ofs _ _ (eq_refl _) P).
      remember ((Mem.mem_contents m') # b) as q. unfold decode_val in H0. 
      destruct chunk; simpl in *; try solve [destruct (ZMap.get ofs q); try discriminate]. 
      + destruct (ZMap.get ofs q); try discriminate.
        destruct (ZMap.get (ofs +1) q); try discriminate.
      + destruct (ZMap.get ofs q); try discriminate.
        destruct (ZMap.get (ofs +1) q); try discriminate.
      + destruct (ZMap.get ofs q); try discriminate.
        ++ destruct (ZMap.get (ofs +1) q); try discriminate.
           destruct (ZMap.get (ofs +1+1) q); try discriminate.
           destruct (ZMap.get (ofs +1+1 +1) q); try discriminate.
        ++ destruct (Val.eq v v && quantity_eq Q32 q0 &&
         match n with
         | 0%nat => false
         | 1%nat => false
         | 2%nat => false
         | 3%nat => true
         | S (S (S (S _))) => false
         end &&
         match ZMap.get (ofs + 1) q with
         | Undef => false
         | Byte _ => false
         | Fragment v' q' m' =>
             Val.eq v v' && quantity_eq Q32 q' &&
             match m' with
             | 0%nat => false
             | 1%nat => false
             | 2%nat => true
             | S (S (S _)) => false
             end &&
             match ZMap.get (ofs + 1 + 1) q with
             | Undef => false
             | Byte _ => false
             | Fragment v'0 q'0 m'0 =>
                 Val.eq v v'0 && quantity_eq Q32 q'0 &&
                 match m'0 with
                 | 0%nat => false
                 | 1%nat => true
                 | S (S _) => false
                 end &&
                 match ZMap.get (ofs + 1 + 1 + 1) q with
                 | Undef => false
                 | Byte _ => false
                 | Fragment v'1 q'1 m'1 =>
                     Val.eq v v'1 && quantity_eq Q32 q'1 &&
                     match m'1 with
                     | 0%nat => true
                     | S _ => false
                     end && true
                 end
             end
         end). -- destruct v; try discriminate. inv H0. inv mi_memval. inv H0. simpl in H2.
      + destruct (ZMap.get ofs q); try discriminate.
      + destruct (ZMap.get ofs q); try discriminate.
      + destruct (ZMap.get ofs q); try discriminate.
      +
        try destruct (ZMap.get (ofs +1+1) q); try discriminate;
        try destruct (ZMap.get (ofs +1+1+1) q); try discriminate.
      + destruct (ZMap.get ofs (m, t)); try discriminate.
        destruct (ZMap.get (ofs+1) (m, t)); try discriminate.
      + destruct (ZMap.get ofs (m, t)); try discriminate.
        destruct (ZMap.get (ofs+1) (m, t)); try discriminate.
      + destruct (ZMap.get ofs (m, t)); try discriminate.
      + destruct (ZMap.get ofs (m, t)); try discriminate.
      destruct q; simpl in *. destruct chunk; simpl in *.
      + destruct (ZMap.get ofs (m, t)); try discriminate.
      + destruct (ZMap.get ofs (m, t)); try discriminate.
      + destruct (ZMap.get ofs (m, t)); try discriminate.
        destruct (ZMap.get (ofs+1) (m, t)); try discriminate.
      + destruct (ZMap.get ofs (m, t)); try discriminate.
        destruct (ZMap.get (ofs+1) (m, t)); try discriminate.
      + destruct (ZMap.get ofs (m, t)); try discriminate.
      + destruct (ZMap.get ofs (m, t)); try discriminate.
 subst j'. instantiate (1:=v').
      inv B. simpl. constructor.
    inv B; try econstructor. Print vmatch.
    red. econstructor. simpl.
    subst j'. + destruct v; inv B; try constructor.
    apply flatinj_E in J'. destruct J' as [? [? ?]]; subst. eapply PMTOP. apply flatinj_I. 
    eapply VMTOP; eauto. constructor.
  - exploit BC'INV; eauto. intros (b'' & delta & J').
    exploit Mem.loadbytes_inject. eexact IMEM. eauto. eauto. intros (bytes & A & B).
    inv B. inv H3. inv H7. eapply PMTOP; eauto.
  }*)
  (* Conclusions *)
  exists bc'; splitall.
- (* incr *)
  exact INCR.
- (* unchanged *)
  simpl; intros. apply pred_dec_true; auto.
- (* vmatch res 
  eapply VMTOP; eauto.*)
   subst j'. simpl in *. 
- (* genv match *)
  apply genv_match_exten with bc; auto.
  simpl; intros; split; intros.
  rewrite pred_dec_true by (eapply mmatch_below; eauto with va). auto.
  destruct (plt b (Mem.nextblock m)). auto. destruct (j' b); congruence.
  simpl; intros. rewrite pred_dec_true by (eapply mmatch_below; eauto with va). auto.
- (* romatch m' *)
  red; simpl; intros. destruct (plt b (Mem.nextblock m)).
  exploit RO; eauto. intros (R & P & Q).
  split; auto.
  split. apply bmatch_incr with bc; auto. apply bmatch_inv with m; auto.
  intros. eapply Mem.loadbytes_unchanged_on_1. apply RDO. (*Check  external_call_readonly. eapply external_call_readonly; eauto.*)
  auto. intros; red. apply Q.
  intros; red; intros; elim (Q ofs).
  apply FWD; trivial. (*eapply external_call_max_perm with (m2 := m'); eauto.*)
  destruct (j' b); congruence.
- (* mmatch top *)
  constructor; simpl; intros.
  + apply ablock_init_sound. apply SMTOP. simpl; congruence.
  + rewrite PTree.gempty in H0; discriminate.
  + apply SMTOP; auto.
  + apply SMTOP; auto.
  + red; simpl; intros. destruct (plt b (Mem.nextblock m)).
    eapply Plt_le_trans. eauto. apply forward_nextblock; trivial. (*eapply external_call_nextblock; eauto.*)
    destruct (j' b) as [[bx deltax] | ] eqn:J'.
    eapply Mem.valid_block_inject_1; eauto.
    congruence.
- (* nostack *)
  red; simpl; intros. destruct (plt b (Mem.nextblock m)).
  apply NOSTACK; auto.
  destruct (j' b); congruence.
- (* unmapped blocks are invariant *)
  intros. eapply Mem.loadbytes_unchanged_on_1; auto.
  apply UNCH1; auto. intros; red. unfold inj_of_bc; rewrite H0; auto.
Qed.
*)
Definition SIM: Mini_simulation_ext.Mini_simulation_extend RTL_eff_sem RTL_eff_sem ge tge.
eapply (Mini_simulation_ext.Build_Mini_simulation_extend).
+ instantiate (1:= core_ord). apply well_founded_ltof. 
+ split. apply senv_preserved.
  red. unfold ge, tge. admit. (*maybe using isGlobalBlock is more prudent?*) 
+ instantiate (1:= fun d st1 m1 L st2 m2 => 
      d=st1 /\ match_states L st1 m1 st2 m2 /\ (forall b, L b = true -> Mem.valid_block m1 b) /\
      sound_state prog L st1 m1 /\
      mem_respects_readonly ge m1 /\ mem_respects_readonly tge m2).
  intros. destruct H as [? [MS [VBL [SST [MRSrc MRTgt]]]]]; subst d. 
  apply matchstates_extends in MS. apply VBL in H0. split; trivial.
  eapply (Mem.valid_block_extends m1); eassumption. 
+ intros. destruct H as [? [MS [VBL [SST [MRSrc MRTgt]]]]]; subst d. 
  apply matchstates_extends in MS. apply Mem.valid_block_extends; trivial. 
+ admit. (*genv stuff*)
+ (*initialCore*)
  intros. simpl in *. destruct v; inv H; simpl.
  destruct (Int.eq_dec i Int.zero); inv H7.
  remember (Genv.find_funct_ptr ge b) as q; symmetry in Heqq; destruct q; inv H6.
  apply funct_ptr_translated in Heqq.
  destruct Heqq as [? [? [FPTR [? ?]]]]. rewrite FPTR.
  destruct f; inv H7. apply bind_inversion in H. destruct H as [tf [TF HOK]]. inv HOK.  
  rewrite <- (mem_lemmas.Forall2_Zlength H0).
  remember (val_casted.val_has_type_list_func vals1 (sig_args (fn_sig f)) &&
       val_casted.vals_defined vals1) as d; symmetry in Heqd. destruct d; inv H9. simpl in *.
  apply andb_true_iff in Heqd. destruct Heqd.
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
      end Int.max_unsigned); inv H7.
  erewrite vals_lessdef_defined; try eassumption.
  assert (HH: bind (transf_function (romem_for x) f) (fun f' : function => OK (Internal f')) =
     OK (Internal tf)).
  { unfold bind. rewrite TF; trivial. }
  specialize (sig_preserved (romem_for x) (Internal f) (Internal tf)); simpl.
  intros KK; rewrite (KK HH); clear KK.
  erewrite val_list_lessdef_hastype; try eassumption. simpl.
  eexists; eexists; split. reflexivity.
  split. reflexivity.
  split. econstructor; eauto. constructor. apply mem_lemmas.forall_lessdef_val_listless; trivial.
  split. discriminate.
  split. { econstructor. intros. admit. (*TODO econstructor. econstructor. *) }
  split; trivial.
+ (*CoreDiagram*)
  intros. simpl. destruct H0 as [? [MS [VBL [SST [MRSrc MRTgt]]]]]; subst cd. 
  exploit core_diagram; eauto. intros [st2' [m2' [L' [HL1' [HL2' [U' [STEP' [MS' HU]]]]]]]].
  exists st2', m2', st1', L'. intuition.
  - clear HL2'. subst L'. apply orb_true_iff in H0. destruct H0.
       eapply mem_step_forward. eapply effstep_mem. apply H. eauto.
       apply freshblockProp_char in H0. apply H0. 
  - clear HL2'. subst L'. eapply sound_step; eassumption.
  - clear HL2'. exploit semantics_lemmas.mem_step_readonly. eapply effstep_mem. apply H.
    intros [Fwd RD]. eapply mem_respects_readonly_fwd; eauto. 
  - clear HL1'. exploit semantics_lemmas.mem_step_readonly. eapply effstep_mem. apply STEP'.
    intros [Fwd RD]. eapply mem_respects_readonly_fwd; eauto. 
  - exists U'; split; trivial.
    left. apply effstep_plus_one; trivial.
+ (*Halted*)
  intros. destruct H as [? [MS [VBL [SST [MRSrc MRTgt]]]]]; subst cd.
  destruct st1; inv H0. destruct stack; inv H1.
  inv MS. inv STACK. 
  exists v'. intuition. 
+ (*atExternal*)
  intros. destruct st1; inv H0. destruct f; inv H2.
  destruct H as [? [MS [VBL [SST [MRSrc MRTgt]]]]]; subst cd. inv MS. inv TFD.
  intuition; simpl.
  destruct (BuiltinEffects.observableEF_dec e0); inv H1.
  exists args'. split; trivial. apply mem_lemmas.val_listless_forall_lessdef; eassumption.
+ (*afterExternal*)
  intros. destruct st1; inv AtExtSrc. destruct f; inv H0.
  destruct MatchMu as [? [MS [VBL [SST [MRSrc MRTgt]]]]]; subst cd.
  inv MS. inv TFD. simpl in *. destruct (BuiltinEffects.observableEF_dec e0); inv H1. inv AtExtTgt.
  eexists; eexists; eexists. split. reflexivity. split. reflexivity. split. reflexivity.
  split. econstructor; trivial.
  split. intros. apply FwdSrc; eauto.
  split.
  { inv SST. constructor. intros. specialize (H _ H0).
    inv H. (* red in RO. destruct MM.*)
    exploit external_call_match''. eapply FwdSrc. apply GE. apply RO. apply MM. apply NOSTK.
    Focus 2. eapply Mem.extends_inject_compose. eassumption. eapply Mem.neutral_inject.
             red.
Lemma 
val_inject_id
    Focus 2. assert (NI: Mem.inject (Mem.flat_inj (Mem.nextblock m1'))  m1' m2'). admit. apply NI.
     (inj_of_bc bc)
{ red in RDO1. admit. (*should hold*) }
       apply GE. 2: apply RO. 2: apply MM. 2: trivial.
    econstructor; eauto.
    + eapply sound_stack_ext. eapply sound_stack_new_bound.  eassumption.
       apply forward_nextblock; eauto.
       intros. (*
    + eapply sound_stack_new_bound. instantiate (1:=Mem.nextblock m1).
      2: eapply mem_forward_nextblock; apply FwdSrc.
      red in NOSTK.
      eapply sound_stack_inv. eassumption.
      intros. red in mmatch_below.

 eapply sound_stack_ext. eapply sound_stack_new_bound.  eassumption.
       apply forward_nextblock; eauto.
      intros. admit. (*ValueAnalysis not directyly applicable any longer here it seems
(*here's an attemt to specialize what's done in ValueAnalysis - but the auxiliary
use of an etxern_inject doesn't seem to work. Thjis may be a problem for all ValueAnalysis phases.
Or do I miss a fact that bc b = BCinvalid  is a conflict with Plt b (Mem.nextblock m1') ?? *)*)*)
  assert (IINCR: inject_incr (inj_of_bc bc) (Mem.flat_inj (Mem.nextblock m1'))).
  { red; intros. unfold inj_of_bc in H4. remember (bc b0) as d.
    destruct d; inv H4; apply flatinj_I; eapply FwdSrc; apply mmatch_below; congruence. }
  
  set (j' := Mem.flat_inj (Mem.nextblock m1')).
  (*assert (ISEP : inject_separated (inj_of_bc bc) j' m1 m1).
  { red; intros. unfold inj_of_bc in H4. remember (bc b1) as d; symmetry in Heqd. destruct d; try discriminate.
    apply flatinj_E in H5. destruct H5 as [? [? ?]]; subst. red in mmatch_below.*)
  assert (JBELOW: forall b, Plt b (Mem.nextblock m1) -> bc b <> BCinvalid -> j' b = inj_of_bc bc b).
  {
    intros. destruct (inj_of_bc bc b0) as [[b' delta] | ] eqn:EQ.
    eapply IINCR; eauto.
    destruct (j' b0) as [[b'' delta'] | ] eqn:EQ'; auto.
    (*exploit ISEP; eauto. tauto.*)
     unfold inj_of_bc in EQ. destruct (bc b0); congruence.
  }
  (* Part 2: constructing bc' from j' *)
  set (f := fun b => if plt b (Mem.nextblock m1)
                     then bc b
                     else match j' b with None => BCinvalid | Some _ => BCother end).
  assert (F_stack: forall b1 b2, f b1 = BCstack -> f b2 = BCstack -> b1 = b2).
  {
    assert (forall b, f b = BCstack -> bc b = BCstack).
    { unfold f; intros. destruct (plt b0 (Mem.nextblock m1)); auto. destruct (j' b0); discriminate. }
    intros. apply (bc_stack bc); auto.
  }
  assert (F_glob: forall b1 b2 id, f b1 = BCglob id -> f b2 = BCglob id -> b1 = b2).
  {
    assert (forall b id, f b = BCglob id -> bc b = BCglob id).
    { unfold f; intros. destruct (plt b0 (Mem.nextblock m1)); auto. destruct (j' b0); discriminate. }
    intros. eapply (bc_glob bc); eauto.
  }
  set (bc' := BC f F_stack F_glob). unfold f in bc'.
  assert (INCR: bc_incr bc bc').
  {
    red; simpl; intros. apply pred_dec_true. eapply mmatch_below; eauto.
  }
  assert (BC'INV: forall b, bc' b <> BCinvalid -> exists b' delta, j' b = Some(b', delta)).
  {
    simpl; intros. destruct (plt b0 (Mem.nextblock m1)).
    exists b0, 0. subst j'. apply flatinj_I. apply FwdSrc; trivial.
    (* rewrite JBELOW by auto. apply inj_of_bc_valid; auto.*)
    destruct (j' b0) as [[b' delta] | ].
    exists b', delta; auto.
    congruence.
  }
  (* Part 3: injection wrt j' implies matching with top wrt bc' *)
  assert (PMTOP: forall b b' delta ofs, j' b = Some (b', delta) -> pmatch bc' b ofs Ptop).
  { clear BC'INV.
    intros. constructor. simpl; unfold f.
    destruct (plt b0 (Mem.nextblock m1)).
    + intros N. subst j'. apply flatinj_E in H4. destruct H4 as [? [? ?]]; subst. 
       admit. (*Contradiction?*)
    + rewrite H4. congruence.
  }
  assert (VMTOP: forall v v', Val.inject j' v v' -> vmatch bc' v Vtop).
  {
    intros. inv H4; constructor. eapply PMTOP; eauto.
  }
  assert (SMTOP: forall b, bc' b <> BCinvalid -> smatch bc' m1' b Ptop).
  {
    intros; split; intros.
  - exploit BC'INV; eauto. intros (b' & delta & J').
    exploit Mem.load_extends. eexact MEXT'. eauto. intros (v' & A & B).
    eapply VMTOP; eauto. instantiate (1:=v'). admit. (*needs obsence of wild pointers*) 
  - exploit BC'INV; eauto. intros (b'' & delta & J').
    exploit Mem.loadbytes_extends. eexact MEXT'. eauto. intros (bytes' & A & B).
    inv B. inv H10. inv H8. inv H11. inv H8. eapply PMTOP; eauto. apply flatinj_I. admit. (*needs obsence of wild pointers*)
  }
  (* Conclusions *)
  erewrite <- Mem.loadbytes_unchanged_on_1 ; auto. 
  assert (JBELOW: forall b, Plt b (Mem.nextblock m1) -> Mem.flat_inj (Mem.nextblock m1') b = inj_of_bc bc b).
  {
    intros. destruct (inj_of_bc bc b0) as [[b' delta] | ] eqn:EQ. 
    eapply IINCR; eauto. 
    destruct (Mem.flat_inj (Mem.nextblock m1') b0) as [[b'' delta'] | ] eqn:EQ'; auto.
    apply flatinj_E in EQ'. destruct EQ' as [? [? ?]]. subst.
    exploit ISEP; eauto. tauto.
  }

            intros. unfold bc_below in mmatch_below. red in NOSTK. red in RO. exploit initial_block_classification. sound_stack_public_call with (bound' := Mem.nextblock m1) (bc' := bc); eauto.
    inv STK. Print mmatch. red in MM. romatch. exploit sound_stack_public_call. eassumption. econstructor. eapply sound_call_state. with bc'; auto.
  * eapply sound_stack_public_call with (bound' := Mem.nextblock m) (bc' := bc); eauto.
    eapply sound_stack_sub; try eassumption. intros b Hb; rewrite Hb; trivial.
    apply Ple_refl.
    eapply mmatch_below; eauto.
    rewrite Lsp; trivial.
  * intros. exploit list_in_map_inv; eauto. intros (r & P & Q). subst v.
    apply D with (areg ae r). auto with va.
 constructor; intros. inv SST. specialize (H0 _ H). 
         inv H0. econstructor. inv STK. econstructor.
          { eapply sound_stack_ext. eapply sound_stack_new_bound. eassumption. apply forward_nextblock; eauto.
            intros. red in NOSTK. red in RO. exploit initial_block_classification.
  split; eapply mem_respects_readonly_forward'; eassumption. *) *)
Admitted.
(*
(*CompComp adaptation: state adaptation, elimination of trace t*)
Lemma transf_step_correct:
  forall s1 (*t*) m1 s2 m2, step ge s1 m1 (*t*) s2 m2 ->
  forall s1' L1 m1' (MS: match_states L1 s1 m1 s1' m1') (SOUND: sound_state prog s1 m1),
  exists s2' L2 m2', step tge s1' m1' (*t*) s2' m2' /\ match_states L2 s2 m2 s2' m2' /\ sound_state prog s2 m2.
Proof.
  induction 1; intros; inv MS; try (TransfInstr; intro C).

  (* Inop *)
- econstructor; econstructor; econstructor; split.
  eapply exec_Inop; eauto.
  econstructor; eauto.
  eapply analysis_correct_1; eauto. simpl; auto.
  unfold transfer; rewrite H; auto.

  (* Iop *)
- destruct (is_trivial_op op) eqn:TRIV.
+ (* unchanged *)
  exploit eval_operation_lessdef. eapply regs_lessdef_regs; eauto. eauto. eauto.
  intros [v' [A B]].
  econstructor; econstructor; econstructor; split.
  eapply exec_Iop with (v := v'); eauto.
  rewrite <- A. apply eval_operation_preserved. exact symbols_preserved.
  econstructor; eauto.
  eapply analysis_correct_1; eauto. simpl; auto.
  unfold transfer; rewrite H.
  destruct SAT as [valu NH]. eapply add_op_holds; eauto.
  apply set_reg_lessdef; auto.
+ (* possibly optimized *)
  destruct (valnum_regs approx!!pc args) as [n1 vl] eqn:?.
  destruct SAT as [valu1 NH1].
  exploit valnum_regs_holds; eauto. intros (valu2 & NH2 & EQ & AG & P & Q).
  destruct (find_rhs n1 (Op op vl)) as [r|] eqn:?.
* (* replaced by move *)
  exploit find_rhs_sound; eauto. intros (v' & EV & LD).
  assert (v' = v) by (inv EV; congruence). subst v'.
  econstructor; econstructor; econstructor; split.
  eapply exec_Iop; eauto. simpl; eauto.
  econstructor; eauto.
  eapply analysis_correct_1; eauto. simpl; auto.
  unfold transfer; rewrite H.
  eapply add_op_holds; eauto.
  apply set_reg_lessdef; auto.
  eapply Val.lessdef_trans; eauto.
* (* possibly simplified *)
  destruct (reduce operation combine_op n1 op args vl) as [op' args'] eqn:?.
  assert (RES: eval_operation ge sp op' rs##args' m = Some v).
    eapply reduce_sound with (sem := fun op vl => eval_operation ge sp op vl m); eauto.
    intros; eapply combine_op_sound; eauto.
  exploit eval_operation_lessdef. eapply regs_lessdef_regs; eauto. eauto. eauto.
  intros [v' [A B]].
  econstructor; econstructor; econstructor; split.
  eapply exec_Iop with (v := v'); eauto.
  rewrite <- A. apply eval_operation_preserved. exact symbols_preserved.
  econstructor; eauto.
  eapply analysis_correct_1; eauto. simpl; auto.
  unfold transfer; rewrite H.
  eapply add_op_holds; eauto.
  apply set_reg_lessdef; auto.

- (* Iload *)
  destruct (valnum_regs approx!!pc args) as [n1 vl] eqn:?.
  destruct SAT as [valu1 NH1].
  exploit valnum_regs_holds; eauto. intros (valu2 & NH2 & EQ & AG & P & Q).
  destruct (find_rhs n1 (Load chunk addr vl)) as [r|] eqn:?.
+ (* replaced by move *)
  exploit find_rhs_sound; eauto. intros (v' & EV & LD).
  assert (v' = v) by (inv EV; congruence). subst v'.
  econstructor; econstructor; econstructor; split.
  eapply exec_Iop; eauto. simpl; eauto.
  econstructor; eauto.
  eapply analysis_correct_1; eauto. simpl; auto.
  unfold transfer; rewrite H.
  eapply add_load_holds; eauto.
  apply set_reg_lessdef; auto. eapply Val.lessdef_trans; eauto.
+ (* load is preserved, but addressing is possibly simplified *)
  destruct (reduce addressing combine_addr n1 addr args vl) as [addr' args'] eqn:?.
  assert (ADDR: eval_addressing ge sp addr' rs##args' = Some a).
  { eapply reduce_sound with (sem := fun addr vl => eval_addressing ge sp addr vl); eauto.
    intros; eapply combine_addr_sound; eauto. }
  exploit eval_addressing_lessdef. apply regs_lessdef_regs; eauto. eexact ADDR.
  intros [a' [A B]].
  assert (ADDR': eval_addressing tge sp addr' rs'##args' = Some a').
  { rewrite <- A. apply eval_addressing_preserved. exact symbols_preserved. }
  exploit Mem.loadv_extends; eauto.
  intros [v' [X Y]].
  econstructor; econstructor; econstructor; split.
  eapply exec_Iload; eauto.
  econstructor; eauto.
  eapply analysis_correct_1; eauto. simpl; auto.
  unfold transfer; rewrite H.
  eapply add_load_holds; eauto.
  apply set_reg_lessdef; auto.

- (* Istore *)
  destruct (valnum_regs approx!!pc args) as [n1 vl] eqn:?.
  destruct SAT as [valu1 NH1].
  exploit valnum_regs_holds; eauto. intros (valu2 & NH2 & EQ & AG & P & Q).
  destruct (reduce addressing combine_addr n1 addr args vl) as [addr' args'] eqn:?.
  assert (ADDR: eval_addressing ge sp addr' rs##args' = Some a).
  { eapply reduce_sound with (sem := fun addr vl => eval_addressing ge sp addr vl); eauto.
    intros; eapply combine_addr_sound; eauto. }
  exploit eval_addressing_lessdef. apply regs_lessdef_regs; eauto. eexact ADDR.
  intros [a' [A B]].
  assert (ADDR': eval_addressing tge sp addr' rs'##args' = Some a').
  { rewrite <- A. apply eval_addressing_preserved. exact symbols_preserved. }
  exploit Mem.storev_extends; eauto. intros [m'' [X Y]].
  econstructor; econstructor; econstructor; split.
  eapply exec_Istore; eauto.
  econstructor; eauto.
  eapply analysis_correct_1; eauto. simpl; auto.
  unfold transfer; rewrite H.
  InvSoundState.
  eapply add_store_result_hold; eauto.
  eapply kill_loads_after_store_holds; eauto.

- (* Icall *)
  exploit find_function_translated; eauto. intros (cu' & tf & FIND' & TRANSF' & LINK').
  econstructor; econstructor; econstructor; split.
  eapply exec_Icall; eauto.
  eapply sig_preserved; eauto.
  econstructor; eauto.
  eapply match_stackframes_cons with (cu := cu); eauto.
  intros. eapply analysis_correct_1; eauto. simpl; auto.
  unfold transfer; rewrite H.
  exists (fun _ => Vundef); apply empty_numbering_holds.
  (*compcomp: new goal L sp*)
  { inv SOUND. apply H1 in LINK; clear H1. inv LINK. eexists; eexists; split. reflexivity.
    admit. (*TODO: pass L to ValueAnalysis sound_state/stack, and ensure L sp*) }
  apply regs_lessdef_regs; auto.

- (* Itailcall *)
  exploit find_function_translated; eauto. intros (cu' & tf & FIND' & TRANSF' & LINK').
  exploit Mem.free_parallel_extends; eauto. intros [m'' [A B]].
  econstructor; econstructor; econstructor; split.
  eapply exec_Itailcall; eauto.
  eapply sig_preserved; eauto.
  econstructor; eauto.
  apply regs_lessdef_regs; auto.

- (* Ibuiltin *)
  rename H2 into OBS.
  exploit (@eval_builtin_args_lessdef _ ge (fun r => rs#r) (fun r => rs'#r)); eauto.
  intros (vargs' & A & B).
  exploit external_call_mem_extends; eauto.
  intros (v' & m2' & P & Q & R & S).
  econstructor; econstructor; econstructor; split.
  eapply exec_Ibuiltin; eauto.
  eapply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  econstructor; eauto.
  eapply analysis_correct_1; eauto. simpl; auto.
* unfold transfer; rewrite H.
  destruct SAT as [valu NH].
  assert (CASE1: exists valu, numbering_holds valu ge sp (regmap_setres res vres rs) m' empty_numbering).
  { exists valu; apply empty_numbering_holds. }
  assert (CASE2: m' = m -> exists valu, numbering_holds valu ge sp (regmap_setres res vres rs) m' (set_res_unknown approx#pc res)).
  { intros. subst m'. exists valu. apply set_res_unknown_holds; auto. }
  assert (CASE3: exists valu, numbering_holds valu ge sp (regmap_setres res vres rs) m'
                         (set_res_unknown (kill_all_loads approx#pc) res)).
  { exists valu. apply set_res_unknown_holds. eapply kill_all_loads_hold; eauto. }
  destruct ef.
  + apply CASE1.
  + apply CASE3.
  + apply CASE1.
  + apply CASE2; inv H1; auto.
  + apply CASE3.
  + apply CASE1.
  + apply CASE1.
  + inv H0; auto. inv H3; auto. inv H4; auto.
    simpl in H1. inv H1.
    exists valu.
    apply set_res_unknown_holds.
    InvSoundState. unfold vanalyze; rewrite AN.
    assert (pmatch bc bsrc osrc (aaddr_arg (VA.State ae am) a0))
    by (eapply aaddr_arg_sound_1; eauto).
    assert (pmatch bc bdst odst (aaddr_arg (VA.State ae am) a1))
    by (eapply aaddr_arg_sound_1; eauto).
    eapply add_memcpy_holds; eauto.
    eapply kill_loads_after_storebytes_holds; eauto.
    eapply Mem.loadbytes_length; eauto.
    simpl. apply Ple_refl.
  + apply CASE2; inv H1; auto.
  + apply CASE2; inv H1; auto.
  + apply CASE1.
  + apply CASE2; inv H1; auto.
* apply set_res_lessdef; auto.

- (* Icond *)
  destruct (valnum_regs approx!!pc args) as [n1 vl] eqn:?.
  elim SAT; intros valu1 NH1.
  exploit valnum_regs_holds; eauto. intros (valu2 & NH2 & EQ & AG & P & Q).
  destruct (reduce condition combine_cond n1 cond args vl) as [cond' args'] eqn:?.
  assert (RES: eval_condition cond' rs##args' m = Some b).
  { eapply reduce_sound with (sem := fun cond vl => eval_condition cond vl m); eauto.
    intros; eapply combine_cond_sound; eauto. }
  econstructor; econstructor; econstructor; split.
  eapply exec_Icond; eauto.
  eapply eval_condition_lessdef; eauto. apply regs_lessdef_regs; auto.
  econstructor; eauto.
  destruct b; eapply analysis_correct_1; eauto; simpl; auto;
  unfold transfer; rewrite H; auto.

- (* Ijumptable *)
  generalize (RLD arg); rewrite H0; intro LD; inv LD.
  econstructor; econstructor; econstructor; split.
  eapply exec_Ijumptable; eauto.
  econstructor; eauto.
  eapply analysis_correct_1; eauto. simpl. eapply list_nth_z_in; eauto.
  unfold transfer; rewrite H; auto.

- (* Ireturn *)
  exploit Mem.free_parallel_extends; eauto. intros [m'' [A B]].
  econstructor; econstructor; econstructor; split.
  eapply exec_Ireturn; eauto.
  econstructor; eauto.
  destruct or; simpl; auto.

- (* internal function *)
  monadInv TFD. unfold transf_function in EQ. fold (analyze cu f) in EQ.
  destruct (analyze cu f) as [approx|] eqn:?; inv EQ.
  exploit Mem.alloc_extends; eauto. apply Zle_refl. apply Zle_refl.
  intros (m'' & A & B).
  econstructor; econstructor; econstructor; split.
  eapply exec_function_internal; simpl; eauto.
  simpl. econstructor; eauto.
  eapply analysis_correct_entry; eauto.
  apply init_regs_lessdef; auto.

- (* external function - now nonobservable *)
  monadInv TFD.
  exploit external_call_mem_extends; eauto.
  intros (v' & m2' & P & Q & R & S).
  econstructor; econstructor; econstructor; split.
  eapply exec_function_external; eauto.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  econstructor; eauto.

- (* return *)
  inv STACK.
  econstructor; econstructor; econstructor; split.
  eapply exec_return; eauto.
  econstructor; eauto.
  apply set_reg_lessdef; auto.
Qed.

Lemma transf_step_correct:
  forall s1 (*t*) m1 s2 m2, step ge s1 m1 (*t*) s2 m2 ->
  forall s1' L1 m1' (MS: match_states L1 s1 m1 s1' m1') (SOUND: sound_state prog s1 m1),
  exists s2' L2 m2', step tge s1' m1' (*t*) s2' m2' /\ match_states L2 s2 m2 s2' m2'.
Proof.
  induction 1; intros; inv MS; try (TransfInstr; intro C).

  (* Inop *)
- econstructor; econstructor; econstructor; split.
  eapply exec_Inop; eauto.
  econstructor; eauto.
  eapply analysis_correct_1; eauto. simpl; auto.
  unfold transfer; rewrite H; auto.

  (* Iop *)
- destruct (is_trivial_op op) eqn:TRIV.
+ (* unchanged *)
  exploit eval_operation_lessdef. eapply regs_lessdef_regs; eauto. eauto. eauto.
  intros [v' [A B]].
  econstructor; econstructor; econstructor; split.
  eapply exec_Iop with (v := v'); eauto.
  rewrite <- A. apply eval_operation_preserved. exact symbols_preserved.
  econstructor; eauto.
  eapply analysis_correct_1; eauto. simpl; auto.
  unfold transfer; rewrite H.
  destruct SAT as [valu NH]. eapply add_op_holds; eauto.
  apply set_reg_lessdef; auto.
+ (* possibly optimized *)
  destruct (valnum_regs approx!!pc args) as [n1 vl] eqn:?.
  destruct SAT as [valu1 NH1].
  exploit valnum_regs_holds; eauto. intros (valu2 & NH2 & EQ & AG & P & Q).
  destruct (find_rhs n1 (Op op vl)) as [r|] eqn:?.
* (* replaced by move *)
  exploit find_rhs_sound; eauto. intros (v' & EV & LD).
  assert (v' = v) by (inv EV; congruence). subst v'.
  econstructor; econstructor; econstructor; split.
  eapply exec_Iop; eauto. simpl; eauto.
  econstructor; eauto.
  eapply analysis_correct_1; eauto. simpl; auto.
  unfold transfer; rewrite H.
  eapply add_op_holds; eauto.
  apply set_reg_lessdef; auto.
  eapply Val.lessdef_trans; eauto.
* (* possibly simplified *)
  destruct (reduce operation combine_op n1 op args vl) as [op' args'] eqn:?.
  assert (RES: eval_operation ge sp op' rs##args' m = Some v).
    eapply reduce_sound with (sem := fun op vl => eval_operation ge sp op vl m); eauto.
    intros; eapply combine_op_sound; eauto.
  exploit eval_operation_lessdef. eapply regs_lessdef_regs; eauto. eauto. eauto.
  intros [v' [A B]].
  econstructor; econstructor; econstructor; split.
  eapply exec_Iop with (v := v'); eauto.
  rewrite <- A. apply eval_operation_preserved. exact symbols_preserved.
  econstructor; eauto.
  eapply analysis_correct_1; eauto. simpl; auto.
  unfold transfer; rewrite H.
  eapply add_op_holds; eauto.
  apply set_reg_lessdef; auto.

- (* Iload *)
  destruct (valnum_regs approx!!pc args) as [n1 vl] eqn:?.
  destruct SAT as [valu1 NH1].
  exploit valnum_regs_holds; eauto. intros (valu2 & NH2 & EQ & AG & P & Q).
  destruct (find_rhs n1 (Load chunk addr vl)) as [r|] eqn:?.
+ (* replaced by move *)
  exploit find_rhs_sound; eauto. intros (v' & EV & LD).
  assert (v' = v) by (inv EV; congruence). subst v'.
  econstructor; econstructor; econstructor; split.
  eapply exec_Iop; eauto. simpl; eauto.
  econstructor; eauto.
  eapply analysis_correct_1; eauto. simpl; auto.
  unfold transfer; rewrite H.
  eapply add_load_holds; eauto.
  apply set_reg_lessdef; auto. eapply Val.lessdef_trans; eauto.
+ (* load is preserved, but addressing is possibly simplified *)
  destruct (reduce addressing combine_addr n1 addr args vl) as [addr' args'] eqn:?.
  assert (ADDR: eval_addressing ge sp addr' rs##args' = Some a).
  { eapply reduce_sound with (sem := fun addr vl => eval_addressing ge sp addr vl); eauto.
    intros; eapply combine_addr_sound; eauto. }
  exploit eval_addressing_lessdef. apply regs_lessdef_regs; eauto. eexact ADDR.
  intros [a' [A B]].
  assert (ADDR': eval_addressing tge sp addr' rs'##args' = Some a').
  { rewrite <- A. apply eval_addressing_preserved. exact symbols_preserved. }
  exploit Mem.loadv_extends; eauto.
  intros [v' [X Y]].
  econstructor; econstructor; econstructor; split.
  eapply exec_Iload; eauto.
  econstructor; eauto.
  eapply analysis_correct_1; eauto. simpl; auto.
  unfold transfer; rewrite H.
  eapply add_load_holds; eauto.
  apply set_reg_lessdef; auto.

- (* Istore *)
  destruct (valnum_regs approx!!pc args) as [n1 vl] eqn:?.
  destruct SAT as [valu1 NH1].
  exploit valnum_regs_holds; eauto. intros (valu2 & NH2 & EQ & AG & P & Q).
  destruct (reduce addressing combine_addr n1 addr args vl) as [addr' args'] eqn:?.
  assert (ADDR: eval_addressing ge sp addr' rs##args' = Some a).
  { eapply reduce_sound with (sem := fun addr vl => eval_addressing ge sp addr vl); eauto.
    intros; eapply combine_addr_sound; eauto. }
  exploit eval_addressing_lessdef. apply regs_lessdef_regs; eauto. eexact ADDR.
  intros [a' [A B]].
  assert (ADDR': eval_addressing tge sp addr' rs'##args' = Some a').
  { rewrite <- A. apply eval_addressing_preserved. exact symbols_preserved. }
  exploit Mem.storev_extends; eauto. intros [m'' [X Y]].
  econstructor; econstructor; econstructor; split.
  eapply exec_Istore; eauto.
  econstructor; eauto.
  eapply analysis_correct_1; eauto. simpl; auto.
  unfold transfer; rewrite H.
  InvSoundState.
  eapply add_store_result_hold; eauto.
  eapply kill_loads_after_store_holds; eauto.

- (* Icall *)
  exploit find_function_translated; eauto. intros (cu' & tf & FIND' & TRANSF' & LINK').
  econstructor; econstructor; econstructor; split.
  eapply exec_Icall; eauto.
  eapply sig_preserved; eauto.
  econstructor; eauto.
  eapply match_stackframes_cons with (cu := cu); eauto.
  intros. eapply analysis_correct_1; eauto. simpl; auto.
  unfold transfer; rewrite H.
  exists (fun _ => Vundef); apply empty_numbering_holds.
  (*compcomp: new goal L sp*)
  { inv SOUND. apply H1 in LINK; clear H1. inv LINK. eexists; eexists; split. reflexivity.
    admit. (*TODO: pass L to ValueAnalysis sound_state/stack, and ensure L sp*) }
  apply regs_lessdef_regs; auto.

- (* Itailcall *)
  exploit find_function_translated; eauto. intros (cu' & tf & FIND' & TRANSF' & LINK').
  exploit Mem.free_parallel_extends; eauto. intros [m'' [A B]].
  econstructor; econstructor; econstructor; split.
  eapply exec_Itailcall; eauto.
  eapply sig_preserved; eauto.
  econstructor; eauto.
  apply regs_lessdef_regs; auto.

- (* Ibuiltin *)
  rename H2 into OBS.
  exploit (@eval_builtin_args_lessdef _ ge (fun r => rs#r) (fun r => rs'#r)); eauto.
  intros (vargs' & A & B).
  exploit external_call_mem_extends; eauto.
  intros (v' & m2' & P & Q & R & S).
  econstructor; econstructor; econstructor; split.
  eapply exec_Ibuiltin; eauto.
  eapply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  econstructor; eauto.
  eapply analysis_correct_1; eauto. simpl; auto.
* unfold transfer; rewrite H.
  destruct SAT as [valu NH].
  assert (CASE1: exists valu, numbering_holds valu ge sp (regmap_setres res vres rs) m' empty_numbering).
  { exists valu; apply empty_numbering_holds. }
  assert (CASE2: m' = m -> exists valu, numbering_holds valu ge sp (regmap_setres res vres rs) m' (set_res_unknown approx#pc res)).
  { intros. subst m'. exists valu. apply set_res_unknown_holds; auto. }
  assert (CASE3: exists valu, numbering_holds valu ge sp (regmap_setres res vres rs) m'
                         (set_res_unknown (kill_all_loads approx#pc) res)).
  { exists valu. apply set_res_unknown_holds. eapply kill_all_loads_hold; eauto. }
  destruct ef.
  + apply CASE1.
  + apply CASE3.
  + apply CASE1.
  + apply CASE2; inv H1; auto.
  + apply CASE3.
  + apply CASE1.
  + apply CASE1.
  + inv H0; auto. inv H3; auto. inv H4; auto.
    simpl in H1. inv H1.
    exists valu.
    apply set_res_unknown_holds.
    InvSoundState. unfold vanalyze; rewrite AN.
    assert (pmatch bc bsrc osrc (aaddr_arg (VA.State ae am) a0))
    by (eapply aaddr_arg_sound_1; eauto).
    assert (pmatch bc bdst odst (aaddr_arg (VA.State ae am) a1))
    by (eapply aaddr_arg_sound_1; eauto).
    eapply add_memcpy_holds; eauto.
    eapply kill_loads_after_storebytes_holds; eauto.
    eapply Mem.loadbytes_length; eauto.
    simpl. apply Ple_refl.
  + apply CASE2; inv H1; auto.
  + apply CASE2; inv H1; auto.
  + apply CASE1.
  + apply CASE2; inv H1; auto.
* apply set_res_lessdef; auto.

- (* Icond *)
  destruct (valnum_regs approx!!pc args) as [n1 vl] eqn:?.
  elim SAT; intros valu1 NH1.
  exploit valnum_regs_holds; eauto. intros (valu2 & NH2 & EQ & AG & P & Q).
  destruct (reduce condition combine_cond n1 cond args vl) as [cond' args'] eqn:?.
  assert (RES: eval_condition cond' rs##args' m = Some b).
  { eapply reduce_sound with (sem := fun cond vl => eval_condition cond vl m); eauto.
    intros; eapply combine_cond_sound; eauto. }
  econstructor; econstructor; econstructor; split.
  eapply exec_Icond; eauto.
  eapply eval_condition_lessdef; eauto. apply regs_lessdef_regs; auto.
  econstructor; eauto.
  destruct b; eapply analysis_correct_1; eauto; simpl; auto;
  unfold transfer; rewrite H; auto.

- (* Ijumptable *)
  generalize (RLD arg); rewrite H0; intro LD; inv LD.
  econstructor; econstructor; econstructor; split.
  eapply exec_Ijumptable; eauto.
  econstructor; eauto.
  eapply analysis_correct_1; eauto. simpl. eapply list_nth_z_in; eauto.
  unfold transfer; rewrite H; auto.

- (* Ireturn *)
  exploit Mem.free_parallel_extends; eauto. intros [m'' [A B]].
  econstructor; econstructor; econstructor; split.
  eapply exec_Ireturn; eauto.
  econstructor; eauto.
  destruct or; simpl; auto.

- (* internal function *)
  monadInv TFD. unfold transf_function in EQ. fold (analyze cu f) in EQ.
  destruct (analyze cu f) as [approx|] eqn:?; inv EQ.
  exploit Mem.alloc_extends; eauto. apply Zle_refl. apply Zle_refl.
  intros (m'' & A & B).
  econstructor; econstructor; econstructor; split.
  eapply exec_function_internal; simpl; eauto.
  simpl. econstructor; eauto.
  eapply analysis_correct_entry; eauto.
  apply init_regs_lessdef; auto.

- (* external function - now nonobservable *)
  monadInv TFD.
  exploit external_call_mem_extends; eauto.
  intros (v' & m2' & P & Q & R & S).
  econstructor; econstructor; econstructor; split.
  eapply exec_function_external; eauto.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  econstructor; eauto.

- (* return *)
  inv STACK.
  econstructor; econstructor; econstructor; split.
  eapply exec_return; eauto.
  econstructor; eauto.
  apply set_reg_lessdef; auto.
Qed.

Lemma transf_initial_states:
  forall st1, initial_state prog st1 ->
  exists st2, initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inversion H.
  exploit funct_ptr_translated; eauto. intros (cu & tf & A & B & C).
  exists (Callstate nil tf nil m0); split.
  econstructor; eauto.
  eapply (Genv.init_mem_match TRANSF); eauto.
  replace (prog_main tprog) with (prog_main prog).
  rewrite symbols_preserved. eauto.
  symmetry. eapply match_program_main; eauto.
  rewrite <- H3. eapply sig_preserved; eauto.
  econstructor. eauto. constructor. auto. auto. apply Mem.extends_refl.
Qed.

Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> final_state st1 r -> final_state st2 r.
Proof.
  intros. inv H0. inv H. inv RES. inv STACK. constructor.
Qed.

Theorem transf_program_correct:
  forward_simulation (RTL.semantics prog) (RTL.semantics tprog).
Proof.
  eapply forward_simulation_step with
    (match_states := fun s1 s2 => sound_state prog s1 /\ match_states s1 s2).
- apply senv_preserved.
- intros. exploit transf_initial_states; eauto. intros [s2 [A B]].
  exists s2. split. auto. split. apply sound_initial; auto. auto.
- intros. destruct H. eapply transf_final_states; eauto.
- intros. destruct H0. exploit transf_step_correct; eauto.
  intros [s2' [A B]]. exists s2'; split. auto. split. eapply sound_step; eauto. auto.
Qed.
*)
End PRESERVATION.
