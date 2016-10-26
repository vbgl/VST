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

(** RTL function inlining: semantic preservation *)

Require Import Coqlib minisepcomp.Wfsimpl compcert.lib.Maps compcert.common.Errors Integers.
Require Import AST Linking Values Memory Globalenvs Events Smallstep.
Require Import minisepcomp.Op minisepcomp.Registers minisepcomp.RTL_memsem.
Require Import minisepcomp.Inlining minisepcomp.Inliningspec.

(*COMCOMP adaptation: additional imports*)
Require Import sepcomp.mem_lemmas.
Require Import minisepcomp.mini_simulations.
Require Import minisepcomp.mini_simulations_lemmas.
Require Import minisepcomp.BuiltinEffects.

Definition match_prog (prog tprog: program) :=
  match_program (fun cunit f tf => transf_fundef (funenv_program cunit) f = OK tf) eq prog tprog.

Lemma transf_program_match:
  forall prog tprog, transf_program prog = OK tprog -> match_prog prog tprog.
Proof.
  intros. eapply match_transform_partial_program_contextual; eauto.
Qed.

Section INLINING.

Variable prog: program.
Variable tprog: program.
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
  forall (v: val) (f: fundef),
  Genv.find_funct ge v = Some f ->
  exists cu f', Genv.find_funct tge v = Some f' /\ transf_fundef (funenv_program cu) f = OK f' /\ linkorder cu prog.
Proof (Genv.find_funct_match TRANSF).

Lemma function_ptr_translated:
  forall (b: block) (f: fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists cu f', Genv.find_funct_ptr tge b = Some f' /\ transf_fundef (funenv_program cu) f = OK f' /\ linkorder cu prog.
Proof (Genv.find_funct_ptr_match TRANSF).

Lemma sig_function_translated:
  forall cu f f', transf_fundef (funenv_program cu) f = OK f' -> funsig f' = funsig f.
Proof.
  intros. destruct f; Errors.monadInv H.
  exploit transf_function_spec; eauto. intros SP; inv SP. auto.
  auto.
Qed.

(** ** Properties of contexts and relocations *)

Remark sreg_below_diff:
  forall ctx r r', Plt r' ctx.(dreg) -> sreg ctx r <> r'.
Proof.
  intros. zify. unfold sreg; rewrite shiftpos_eq. xomega.
Qed.

Remark context_below_diff:
  forall ctx1 ctx2 r1 r2,
  context_below ctx1 ctx2 -> Ple r1 ctx1.(mreg) -> sreg ctx1 r1 <> sreg ctx2 r2.
Proof.
  intros. red in H. zify. unfold sreg; rewrite ! shiftpos_eq. xomega.
Qed.

Remark context_below_lt:
  forall ctx1 ctx2 r, context_below ctx1 ctx2 -> Ple r ctx1.(mreg) -> Plt (sreg ctx1 r) ctx2.(dreg).
Proof.
  intros. red in H. unfold Plt; zify. unfold sreg; rewrite shiftpos_eq.
  xomega.
Qed.

(*
Remark context_below_le:
  forall ctx1 ctx2 r, context_below ctx1 ctx2 -> Ple r ctx1.(mreg) -> Ple (sreg ctx1 r) ctx2.(dreg).
Proof.
  intros. red in H. unfold Ple; zify. unfold sreg; rewrite shiftpos_eq.
  xomega.
Qed.
*)

(** ** Agreement between register sets before and after inlining. *)

Definition agree_regs (F: meminj) (ctx: context) (rs rs': regset) :=
  (forall r, Ple r ctx.(mreg) -> Val.inject F rs#r rs'#(sreg ctx r))
/\(forall r, Plt ctx.(mreg) r -> rs#r = Vundef).

Definition val_reg_charact (F: meminj) (ctx: context) (rs': regset) (v: val) (r: reg) :=
  (Plt ctx.(mreg) r /\ v = Vundef) \/ (Ple r ctx.(mreg) /\ Val.inject F v rs'#(sreg ctx r)).

Remark Plt_Ple_dec:
  forall p q, {Plt p q} + {Ple q p}.
Proof.
  intros. destruct (plt p q). left; auto. right; xomega.
Qed.

Lemma agree_val_reg_gen:
  forall F ctx rs rs' r, agree_regs F ctx rs rs' -> val_reg_charact F ctx rs' rs#r r.
Proof.
  intros. destruct H as [A B].
  destruct (Plt_Ple_dec (mreg ctx) r).
  left. rewrite B; auto.
  right. auto.
Qed.

Lemma agree_val_regs_gen:
  forall F ctx rs rs' rl,
  agree_regs F ctx rs rs' -> list_forall2 (val_reg_charact F ctx rs') rs##rl rl.
Proof.
  induction rl; intros; constructor; auto. apply agree_val_reg_gen; auto.
Qed.

Lemma agree_val_reg:
  forall F ctx rs rs' r, agree_regs F ctx rs rs' -> Val.inject F rs#r rs'#(sreg ctx r).
Proof.
  intros. exploit agree_val_reg_gen; eauto. instantiate (1 := r). intros [[A B] | [A B]].
  rewrite B; auto.
  auto.
Qed.

Lemma agree_val_regs:
  forall F ctx rs rs' rl, agree_regs F ctx rs rs' -> Val.inject_list F rs##rl rs'##(sregs ctx rl).
Proof.
  induction rl; intros; simpl. constructor. constructor; auto. apply agree_val_reg; auto.
Qed.

Lemma agree_set_reg:
  forall F ctx rs rs' r v v',
  agree_regs F ctx rs rs' ->
  Val.inject F v v' ->
  Ple r ctx.(mreg) ->
  agree_regs F ctx (rs#r <- v) (rs'#(sreg ctx r) <- v').
Proof.
  unfold agree_regs; intros. destruct H. split; intros.
  repeat rewrite Regmap.gsspec.
  destruct (peq r0 r). subst r0. rewrite peq_true. auto.
  rewrite peq_false. auto. apply shiftpos_diff; auto.
  rewrite Regmap.gso. auto. xomega.
Qed.

Lemma agree_set_reg_undef:
  forall F ctx rs rs' r v',
  agree_regs F ctx rs rs' ->
  agree_regs F ctx (rs#r <- Vundef) (rs'#(sreg ctx r) <- v').
Proof.
  unfold agree_regs; intros. destruct H. split; intros.
  repeat rewrite Regmap.gsspec.
  destruct (peq r0 r). subst r0. rewrite peq_true. auto.
  rewrite peq_false. auto. apply shiftpos_diff; auto.
  rewrite Regmap.gsspec. destruct (peq r0 r); auto.
Qed.

Lemma agree_set_reg_undef':
  forall F ctx rs rs' r,
  agree_regs F ctx rs rs' ->
  agree_regs F ctx (rs#r <- Vundef) rs'.
Proof.
  unfold agree_regs; intros. destruct H. split; intros.
  rewrite Regmap.gsspec.
  destruct (peq r0 r). subst r0. auto. auto.
  rewrite Regmap.gsspec. destruct (peq r0 r); auto.
Qed.

Lemma agree_regs_invariant:
  forall F ctx rs rs1 rs2,
  agree_regs F ctx rs rs1 ->
  (forall r, Ple ctx.(dreg) r -> Plt r (ctx.(dreg) + ctx.(mreg)) -> rs2#r = rs1#r) ->
  agree_regs F ctx rs rs2.
Proof.
  unfold agree_regs; intros. destruct H. split; intros.
  rewrite H0. auto.
  apply shiftpos_above.
  eapply Plt_le_trans. apply shiftpos_below. xomega.
  apply H1; auto.
Qed.

Lemma agree_regs_incr:
  forall F ctx rs1 rs2 F',
  agree_regs F ctx rs1 rs2 ->
  inject_incr F F' ->
  agree_regs F' ctx rs1 rs2.
Proof.
  intros. destruct H. split; intros. eauto. auto.
Qed.

Remark agree_regs_init:
  forall F ctx rs, agree_regs F ctx (Regmap.init Vundef) rs.
Proof.
  intros; split; intros. rewrite Regmap.gi; auto. rewrite Regmap.gi; auto.
Qed.

Lemma agree_regs_init_regs:
  forall F ctx rl vl vl',
  Val.inject_list F vl vl' ->
  (forall r, In r rl -> Ple r ctx.(mreg)) ->
  agree_regs F ctx (init_regs vl rl) (init_regs vl' (sregs ctx rl)).
Proof.
  induction rl; simpl; intros.
  apply agree_regs_init.
  inv H. apply agree_regs_init.
  apply agree_set_reg; auto.
Qed.

(** ** Executing sequences of moves *)
Require Import sepcomp.semantics_lemmas.
Require Import sepcomp.effect_semantics.
Require Import msl.Axioms. (*for extensionality*)

(*COMCOMP adaptation: use refactored states, assert that execution has EmptyEffect *)
Lemma tr_moves_init_regs:
  forall F stk f sp m ctx1 ctx2, context_below ctx1 ctx2 ->
  forall rdsts rsrcs vl pc1 pc2 rs1,
  tr_moves f.(fn_code) pc1 (sregs ctx1 rsrcs) (sregs ctx2 rdsts) pc2 ->
  (forall r, In r rdsts -> Ple r ctx2.(mreg)) ->
  list_forall2 (val_reg_charact F ctx1 rs1) vl rsrcs ->
  exists rs2,
    effstep_star RTL_eff_sem tge EmptyEffect (State stk f sp pc1 rs1) m
               (*E0*) (State stk f sp pc2 rs2) m
  /\ agree_regs F ctx2 (init_regs vl rdsts) rs2
  /\ forall r, Plt r ctx2.(dreg) -> rs2#r = rs1#r.
Proof.
  induction rdsts; simpl; intros.
(* rdsts = nil *)
  inv H0. exists rs1; split. apply effstep_star_zero. split. apply agree_regs_init. auto.
(* rdsts = a :: rdsts *)
  inv H2. inv H0.
  exists rs1; split. apply effstep_star_zero. split. apply agree_regs_init. auto.
  simpl in H0. inv H0.
  exploit IHrdsts; eauto. intros [rs2 [A [B C]]].
  exists (rs2#(sreg ctx2 a) <- (rs2#(sreg ctx1 b1))).

  split. eapply effstep_star_trans'. eauto. apply effstep_star_one. eapply effexec_Iop; eauto. (* traceEq.*)
         (*New:*) extensionality b. extensionality z. unfold EmptyEffect. reflexivity.
  split. destruct H3 as [[P Q] | [P Q]].
  subst a1. eapply agree_set_reg_undef; eauto.
  eapply agree_set_reg; eauto. rewrite C; auto.  apply context_below_lt; auto.
  intros. rewrite Regmap.gso. auto. apply sym_not_equal. eapply sreg_below_diff; eauto.
  destruct H2; discriminate.
Qed.

(** ** Memory invariants *)

(** A stack location is private if it is not the image of a valid
   location and we have full rights on it. *)

Definition loc_private (F: meminj) (m m': mem) (sp: block) (ofs: Z) : Prop :=
  Mem.perm m' sp ofs Cur Freeable /\
  (forall b delta, F b = Some(sp, delta) -> ~Mem.perm m b (ofs - delta) Max Nonempty).

(** Likewise, for a range of locations. *)

(*COMPCOMP adaptation: added parameter L', and ensure that sp is local block in TGT*)
Definition range_private (L': block -> bool) (F: meminj) (m m': mem) (sp: block) (lo hi: Z) : Prop :=
  L' sp = true /\ (forall ofs, lo <= ofs < hi -> loc_private F m m' sp ofs).

Lemma range_private_invariant:
  forall L' F m m' sp lo hi F1 m1 m1',
  range_private L' F m m' sp lo hi ->
  (forall b delta ofs,
      F1 b = Some(sp, delta) ->
      Mem.perm m1 b ofs Max Nonempty ->
      lo <= ofs + delta < hi ->
      F b = Some(sp, delta) /\ Mem.perm m b ofs Max Nonempty) ->
  (forall ofs, Mem.perm m' sp ofs Cur Freeable -> Mem.perm m1' sp ofs Cur Freeable) ->
  range_private L' F1 m1 m1' sp lo hi.
Proof.
  intros. destruct H as [Hsp H]. split; trivial. intros.
  exploit H; eauto. intros [A B]. split; auto.
  intros; red; intros. exploit H0; eauto. omega. intros [P Q].
  eelim B; eauto.
Qed.

Lemma range_private_perms:
  forall L' F m m' sp lo hi,
  range_private L' F m m' sp lo hi ->
  Mem.range_perm m' sp lo hi Cur Freeable.
Proof.
  intros; red; intros. eapply H; eauto.
Qed.

Lemma range_private_alloc_left:
  forall L' F m m' sp' base hi sz m1 sp F1,
  range_private L' F m m' sp' base hi ->
  Mem.alloc m 0 sz = (m1, sp) ->
  F1 sp = Some(sp', base) ->
  (forall b, b <> sp -> F1 b = F b) ->
  range_private L' F1 m1 m' sp' (base + Zmax sz 0) hi.
Proof.
  intros. destruct H as [Hsp H]. split; trivial. intros; red; intros. 
  exploit (H ofs). generalize (Zmax2 sz 0). omega. intros [A B].
  split; auto. intros; red; intros.
  exploit Mem.perm_alloc_inv; eauto.
  destruct (eq_block b sp); intros.
  subst b. rewrite H1 in H4; inv H4.
  rewrite Zmax_spec in H3. destruct (zlt 0 sz); omega.
  rewrite H2 in H4; auto. eelim B; eauto.
Qed.

Lemma range_private_free_left:
  forall L' F m m' sp base sz hi b m1,
  range_private L' F m m' sp (base + Zmax sz 0) hi ->
  Mem.free m b 0 sz = Some m1 ->
  F b = Some(sp, base) ->
  Mem.inject F m m' ->
  range_private L' F m1 m' sp base hi.
Proof.
  intros. destruct H as [Hsp H]. split; trivial. intros; red; intros.
  destruct (zlt ofs (base + Zmax sz 0)) as [z|z].
  split.
  replace ofs with ((ofs - base) + base) by omega.
  eapply Mem.perm_inject; eauto.
  eapply Mem.free_range_perm; eauto.
  rewrite Zmax_spec in z. destruct (zlt 0 sz); omega.
  intros; red; intros. destruct (eq_block b b0).
  subst b0. rewrite H1 in H4; inv H4.
  eelim Mem.perm_free_2; eauto. rewrite Zmax_spec in z. destruct (zlt 0 sz); omega.
  exploit Mem.mi_no_overlap; eauto.
  apply Mem.perm_cur_max. apply Mem.perm_implies with Freeable; auto with mem.
  eapply Mem.free_range_perm. eauto.
  instantiate (1 := ofs - base). rewrite Zmax_spec in z. destruct (zlt 0 sz); omega.
  eapply Mem.perm_free_3; eauto.
  intros [A | A]. congruence. omega.

  exploit (H ofs). omega. intros [A B]. split. auto.
  intros; red; intros. eelim B; eauto. eapply Mem.perm_free_3; eauto.
Qed. 

Lemma range_private_extcall:
  forall L2 F F' m1 m2 m1' m2' sp base hi,
  range_private L2 F m1 m1' sp base hi ->
  (forall b ofs p,
     Mem.valid_block m1 b -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p) ->
  (*Mem.unchanged_on (loc_out_of_reach F m1) m1' m2' ->*)
  Mem.unchanged_on (o_o_reach F L2 m1) m1' m2' ->
  Mem.inject F m1 m1' ->

  inject_incr F F' ->
  (*inject_separated F F' m1 m1' ->*)
  (forall b b' d, F b = None -> F' b =  Some(b',d) -> b' <> sp) ->
  Mem.valid_block m1' sp ->
  range_private L2 F' m2 m2' sp base hi.
Proof.
  intros until hi; intros RP PERM UNCH INJ INCR SEP VB. 
  destruct RP as [Hsp RP]. split; trivial; intros.
  red; intros. exploit RP; eauto. intros [A B].
  split. { eapply Mem.perm_unchanged_on; eauto.
           unfold o_o_reach; split; trivial. }
  intros. destruct (F b) as [[sp1 delta1] |] eqn:?.
  exploit INCR; eauto. intros EQ; rewrite H0 in EQ; inv EQ.
  red; intros; eelim B; eauto. eapply PERM; eauto.
  red. destruct (plt b (Mem.nextblock m1)); auto.
  exploit Mem.mi_freeblocks; eauto. congruence.
  exploit SEP; eauto. 
Qed.
(*COMPCOMP adaptation: original statement and proof were
Lemma range_private_extcall:
  forall F F' m1 m2 m1' m2' sp base hi,
  range_private F m1 m1' sp base hi ->
  (forall b ofs p,
     Mem.valid_block m1 b -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p) ->
  Mem.unchanged_on (loc_out_of_reach F m1) m1' m2' ->
  Mem.inject F m1 m1' ->
  inject_incr F F' ->
  inject_separated F F' m1 m1' ->
  Mem.valid_block m1' sp ->
  range_private F' m2 m2' sp base hi.
Proof.
  intros until hi; intros RP PERM UNCH INJ INCR SEP VB.
  red; intros. exploit RP; eauto. intros [A B].
  split. eapply Mem.perm_unchanged_on; eauto.
  intros. red in SEP. destruct (F b) as [[sp1 delta1] |] eqn:?.
  exploit INCR; eauto. intros EQ; rewrite H0 in EQ; inv EQ.
  red; intros; eelim B; eauto. eapply PERM; eauto.
  red. destruct (plt b (Mem.nextblock m1)); auto.
  exploit Mem.mi_freeblocks; eauto. congruence.
  exploit SEP; eauto. tauto.
Qed.*)

(*COMPCOMP adaptation: new*)
Lemma range_private_sub L1 F m m' sp lo hi (RP: range_private L1 F m m' sp lo hi)
         L2 (HL: forall b, L1 b = true -> L2 b = true):
      range_private L2 F m m' sp lo hi.
Proof. destruct RP. split; eauto. Qed.

(** ** Relating global environments *)

Inductive match_globalenvs (F: meminj) (bound: block): Prop :=
  | mk_match_globalenvs
      (DOMAIN: forall b, Plt b bound -> F b = Some(b, 0))
      (IMAGE: forall b1 b2 delta, F b1 = Some(b2, delta) -> Plt b2 bound -> b1 = b2)
      (SYMBOLS: forall id b, Genv.find_symbol ge id = Some b -> Plt b bound)
      (FUNCTIONS: forall b fd, Genv.find_funct_ptr ge b = Some fd -> Plt b bound)
      (VARINFOS: forall b gv, Genv.find_var_info ge b = Some gv -> Plt b bound).

Lemma find_function_agree:
  forall ros rs fd F ctx rs' bound,
  find_function ge ros rs = Some fd ->
  agree_regs F ctx rs rs' ->
  match_globalenvs F bound ->
  exists cu fd',
  find_function tge (sros ctx ros) rs' = Some fd' /\ transf_fundef (funenv_program cu) fd = OK fd' /\ linkorder cu prog.
Proof.
  intros. destruct ros as [r | id]; simpl in *.
- (* register *)
  assert (EQ: rs'#(sreg ctx r) = rs#r).
  { exploit Genv.find_funct_inv; eauto. intros [b EQ].
    assert (A: Val.inject F rs#r rs'#(sreg ctx r)). eapply agree_val_reg; eauto.
    rewrite EQ in A; inv A.
    inv H1. rewrite DOMAIN in H5. inv H5. auto.
    apply FUNCTIONS with fd.
    rewrite EQ in H; rewrite Genv.find_funct_find_funct_ptr in H. auto.
  }
  rewrite EQ. eapply functions_translated; eauto.
- (* symbol *)
  rewrite symbols_preserved. destruct (Genv.find_symbol ge id); try discriminate.
  eapply function_ptr_translated; eauto.
Qed.

Lemma find_inlined_function:
  forall fenv id rs fd f,
  fenv_compat prog fenv ->
  find_function ge (inr id) rs = Some fd ->
  fenv!id = Some f ->
  fd = Internal f.
Proof.
  intros.
  apply H in H1. apply Genv.find_def_symbol in H1. destruct H1 as (b & A & B).
  simpl in H0. unfold ge, fundef in H0. rewrite A in H0.
  rewrite <- Genv.find_funct_ptr_iff in B.
  congruence.
Qed. 

(** Translation of builtin arguments. *)

Lemma tr_builtin_arg:
  forall F bound ctx rs rs' sp sp' m m',
  match_globalenvs F bound ->
  agree_regs F ctx rs rs' ->
  F sp = Some(sp', ctx.(dstk)) ->
  Mem.inject F m m' ->
  forall a v,
  eval_builtin_arg ge (fun r => rs#r) (Vptr sp Int.zero) m a v ->
  exists v', eval_builtin_arg tge (fun r => rs'#r) (Vptr sp' Int.zero) m' (sbuiltinarg ctx a) v'
          /\ Val.inject F v v'.
Proof.
  intros until m'; intros MG AG SP MI. induction 1; simpl.
- exists rs'#(sreg ctx x); split. constructor. eapply agree_val_reg; eauto.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- exploit Mem.loadv_inject; eauto.
  instantiate (1 := Vptr sp' (Int.add ofs (Int.repr (dstk ctx)))).
  simpl. econstructor; eauto. rewrite Int.add_zero_l; auto.
  intros (v' & A & B). exists v'; split; auto. constructor. simpl. rewrite Int.add_zero_l; auto.
- econstructor; split. constructor. simpl. econstructor; eauto. rewrite ! Int.add_zero_l; auto.
- assert (Val.inject F (Senv.symbol_address ge id ofs) (Senv.symbol_address tge id ofs)).
  { unfold Senv.symbol_address; simpl; unfold Genv.symbol_address.
    rewrite symbols_preserved. destruct (Genv.find_symbol ge id) as [b|] eqn:FS; auto.
    inv MG. econstructor. eauto. rewrite Int.add_zero; auto. }
  exploit Mem.loadv_inject; eauto. intros (v' & A & B).
  exists v'; eauto with barg.
- econstructor; split. constructor.
  unfold Senv.symbol_address; simpl; unfold Genv.symbol_address.
  rewrite symbols_preserved. destruct (Genv.find_symbol ge id) as [b|] eqn:FS; auto.
  inv MG. econstructor. eauto. rewrite Int.add_zero; auto.
- destruct IHeval_builtin_arg1 as (v1 & A1 & B1).
  destruct IHeval_builtin_arg2 as (v2 & A2 & B2).
  econstructor; split. eauto with barg. apply Val.longofwords_inject; auto.
Qed.

Lemma tr_builtin_args:
  forall F bound ctx rs rs' sp sp' m m',
  match_globalenvs F bound ->
  agree_regs F ctx rs rs' ->
  F sp = Some(sp', ctx.(dstk)) ->
  Mem.inject F m m' ->
  forall al vl,
  eval_builtin_args ge (fun r => rs#r) (Vptr sp Int.zero) m al vl ->
  exists vl', eval_builtin_args tge (fun r => rs'#r) (Vptr sp' Int.zero) m' (map (sbuiltinarg ctx) al) vl'
          /\ Val.inject_list F vl vl'.
Proof.
  induction 5; simpl.
- exists (@nil val); split; constructor.
- exploit tr_builtin_arg; eauto. intros (v1' & A & B).
  destruct IHlist_forall2 as (vl' & C & D).
  exists (v1' :: vl'); split; constructor; auto.
Qed.

(** ** Relating stacks *)

(*COMPCOMP adaptation: added component L and L', and ensure that stack blocks are local*)
Inductive match_stacks (F: meminj) (m m': mem) (L L': block -> bool) :
             list stackframe -> list stackframe -> block -> Prop :=
  | match_stacks_nil: forall bound1 bound
        (MG: match_globalenvs F bound1)
        (BELOW: Ple bound1 bound)
        (*COMPCOMP new: (GLOBbnd: forall b', Plt b' bound1 -> isGlobalBlock tge b' = true)
         (EXT: forall b', isGlobalBlock tge b' = true -> L' b' = false /\ Mem.valid_block m' b'),*)
        (*COMPCOMP new:*) (GLOBbnd: forall b', Plt b' bound1 -> Plt b' (Genv.genv_next tge))
        (*COMPCOMP new:*) (EXT: forall b', Plt b' (Genv.genv_next tge) -> L' b' = false /\ Mem.valid_block m' b'),
      match_stacks F m m' L L' nil nil bound
  | match_stacks_cons: forall res f sp pc rs stk f' sp' rs' stk' bound fenv ctx 
        (MS: match_stacks_inside F m m' L L' stk stk' f' ctx sp' rs')
        (COMPAT: fenv_compat prog fenv)
        (FB: tr_funbody fenv f'.(fn_stacksize) ctx f f'.(fn_code))
        (AG: agree_regs F ctx rs rs')
        (SP: F sp = Some(sp', ctx.(dstk)))
        (PRIV: range_private L' F m m' sp' (ctx.(dstk) + ctx.(mstk)) f'.(fn_stacksize))
        (SSZ1: 0 <= f'.(fn_stacksize) < Int.max_unsigned)
        (SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs <= f'.(fn_stacksize))
        (RES: Ple res ctx.(mreg))
        (BELOW: Plt sp' bound)
        (Lsp: L sp = true)
        (Lsp': L' sp' = true),
      match_stacks F m m' L L'
                   (Stackframe res f (Vptr sp Int.zero) pc rs :: stk)
                   (Stackframe (sreg ctx res) f' (Vptr sp' Int.zero) (spc ctx pc) rs' :: stk')
                   bound
  | match_stacks_untailcall: forall stk res f' sp' rpc rs' stk' bound ctx
        (MS: match_stacks_inside F m m' L L' stk stk' f' ctx sp' rs')
        (PRIV: range_private L' F m m' sp' ctx.(dstk) f'.(fn_stacksize))
        (SSZ1: 0 <= f'.(fn_stacksize) < Int.max_unsigned)
        (SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs <= f'.(fn_stacksize))
        (RET: ctx.(retinfo) = Some (rpc, res))
        (BELOW: Plt sp' bound)
        (Lsp': L' sp' = true),
      match_stacks F m m' L L'
                   stk
                   (Stackframe res f' (Vptr sp' Int.zero) rpc rs' :: stk')
                   bound

with match_stacks_inside (F: meminj) (m m': mem)(L L': block -> bool):
        list stackframe -> list stackframe -> function -> context -> block -> regset -> Prop :=
  | match_stacks_inside_base: forall stk stk' f' ctx sp' rs'
        (MS: match_stacks F m m' L L' stk stk' sp')
        (RET: ctx.(retinfo) = None)
        (DSTK: ctx.(dstk) = 0)
        (Lsp': L' sp' = true),
      match_stacks_inside F m m' L L' stk stk' f' ctx sp' rs'
  | match_stacks_inside_inlined: forall res f sp pc rs stk stk' f' fenv ctx sp' rs' ctx' 
        (MS: match_stacks_inside F m m' L L' stk stk' f' ctx' sp' rs')
        (COMPAT: fenv_compat prog fenv)
        (FB: tr_funbody fenv f'.(fn_stacksize) ctx' f f'.(fn_code))
        (AG: agree_regs F ctx' rs rs')
        (SP: F sp = Some(sp', ctx'.(dstk)))
        (PAD: range_private L' F m m' sp' (ctx'.(dstk) + ctx'.(mstk)) ctx.(dstk))
        (RES: Ple res ctx'.(mreg))
        (RET: ctx.(retinfo) = Some (spc ctx' pc, sreg ctx' res))
        (BELOW: context_below ctx' ctx)
        (SBELOW: context_stack_call ctx' ctx)
        (Lsp: L sp = true)
        (Lsp': L' sp' = true),
      match_stacks_inside F m m' L L' (Stackframe res f (Vptr sp Int.zero) pc rs :: stk)
                                 stk' f' ctx sp' rs'.

(** Properties of match_stacks *)

Section MATCH_STACKS.

Variable F: meminj.
Variables m m': mem.
(*COMPCOMP adaptation: added the following declations, and added parameters L L' 
 to all match_stacks/match_stacks_inside statementet below*)
Variables L L': block -> bool.

Lemma match_stacks_globalenvs:
  forall stk stk' bound,
  match_stacks F m m' L L' stk stk' bound -> exists b, match_globalenvs F b
with match_stacks_inside_globalenvs:
  forall stk stk' f ctx sp rs',
  match_stacks_inside F m m' L L' stk stk' f ctx sp rs' -> exists b, match_globalenvs F b.
Proof.
  induction 1; eauto.
  induction 1; eauto.
Qed.

Lemma match_globalenvs_preserves_globals:
  forall b, match_globalenvs F b -> meminj_preserves_globals ge F.
Proof.
  intros. inv H. red. split. eauto. split. eauto.
  intros. symmetry. eapply IMAGE; eauto.
Qed.

Lemma match_stacks_inside_globals:
  forall stk stk' f ctx sp rs',
  match_stacks_inside F m m' L L' stk stk' f ctx sp rs' -> meminj_preserves_globals ge F.
Proof.
  intros. exploit match_stacks_inside_globalenvs; eauto. intros [b A].
  eapply match_globalenvs_preserves_globals; eauto.
Qed.

Lemma match_stacks_bound:
  forall stk stk' bound bound1,
  match_stacks F m m' L L' stk stk' bound ->
  Ple bound bound1 ->
  match_stacks F m m' L L' stk stk' bound1.
Proof.
  intros. inv H.
- apply match_stacks_nil with bound0; auto. xomega.
- eapply match_stacks_cons; eauto. xomega. 
- eapply match_stacks_untailcall; eauto. xomega. 
Qed.

(*COMPCOMP new:*)
Lemma match_stacks_inside_sp_local:
  forall stk stk' f ctx sp rs',
  match_stacks_inside F m m' L L' stk stk' f ctx sp rs' -> L' sp = true.
Proof. induction 1; trivial. Qed.

Variable F1: meminj.
Variables m1 m1': mem.
Hypothesis VB': forall b, Mem.valid_block m' b -> Mem.valid_block m1' b.
Hypothesis INCR: inject_incr F F1.

Lemma match_stacks_invariant:
  forall stk stk' bound, match_stacks F m m' L L' stk stk' bound ->
  forall (INJ: forall b1 b2 delta,
               F1 b1 = Some(b2, delta) -> Plt b2 bound -> F b1 = Some(b2, delta))
         (PERM1: forall b1 b2 delta ofs,
               F1 b1 = Some(b2, delta) -> Plt b2 bound ->
               Mem.perm m1 b1 ofs Max Nonempty -> Mem.perm m b1 ofs Max Nonempty)
         (PERM2: forall b ofs, Plt b bound ->
               Mem.perm m' b ofs Cur Freeable -> Mem.perm m1' b ofs Cur Freeable)
         (PERM3: forall b ofs k p, Plt b bound ->
               Mem.perm m1' b ofs k p -> Mem.perm m' b ofs k p),
  match_stacks F1 m1 m1' L L'  stk stk' bound

with match_stacks_inside_invariant:
  forall stk stk' f' ctx sp' rs1,
  match_stacks_inside F m m' L L' stk stk' f' ctx sp' rs1 ->
  forall rs2
         (RS: forall r, Plt r ctx.(dreg) -> rs2#r = rs1#r)
         (INJ: forall b1 b2 delta,
               F1 b1 = Some(b2, delta) -> Ple b2 sp' -> F b1 = Some(b2, delta))
         (PERM1: forall b1 b2 delta ofs,
               F1 b1 = Some(b2, delta) -> Ple b2 sp' ->
               Mem.perm m1 b1 ofs Max Nonempty -> Mem.perm m b1 ofs Max Nonempty)
         (PERM2: forall b ofs, Ple b sp' ->
               Mem.perm m' b ofs Cur Freeable -> Mem.perm m1' b ofs Cur Freeable)
         (PERM3: forall b ofs k p, Ple b sp' ->
               Mem.perm m1' b ofs k p -> Mem.perm m' b ofs k p),
  match_stacks_inside F1 m1 m1' L L' stk stk' f' ctx sp' rs2.

Proof.
- induction 1; intros.
+  (* nil *)
  apply match_stacks_nil with (bound1 := bound1); trivial.
  * inv MG. constructor; auto.
    intros. apply IMAGE with delta. eapply INJ; eauto. eapply Plt_le_trans; eauto.
    auto.
  * intros. destruct (EXT _ H). split; eauto.  
+ (* cons *)
  apply match_stacks_cons with (fenv := fenv) (ctx := ctx); auto.
  * eapply match_stacks_inside_invariant; eauto.
    intros; eapply INJ; eauto; xomega.
    intros; eapply PERM1; eauto; xomega.
    intros; eapply PERM2; eauto; xomega.
    intros; eapply PERM3; eauto; xomega.
  * eapply agree_regs_incr; eauto.
  * eapply range_private_invariant; eauto.
+ (* untailcall *)
  apply match_stacks_untailcall with (ctx := ctx); auto.
  eapply match_stacks_inside_invariant; eauto.
  intros; eapply INJ; eauto; xomega.
  intros; eapply PERM1; eauto; xomega.
  intros; eapply PERM2; eauto; xomega.
  intros; eapply PERM3; eauto; xomega.
  eapply range_private_invariant; eauto.

- induction 1; intros.
+ (* base *)
  eapply match_stacks_inside_base; eauto.
  eapply match_stacks_invariant; eauto.
  intros; eapply INJ; eauto; xomega.
  intros; eapply PERM1; eauto; xomega.
  intros; eapply PERM2; eauto; xomega.
  intros; eapply PERM3; eauto; xomega.
+ (* inlined *)
  apply match_stacks_inside_inlined with (fenv := fenv) (ctx' := ctx'); auto.
  apply IHmatch_stacks_inside; auto.
  intros. apply RS. red in BELOW. xomega.
  apply agree_regs_incr with F; auto.
  apply agree_regs_invariant with rs'; auto.
  intros. apply RS. red in BELOW. xomega.
  eapply range_private_invariant; eauto.
    intros. split. eapply INJ; eauto. xomega. eapply PERM1; eauto. xomega.
    intros. eapply PERM2; eauto. xomega.
Qed.

Lemma match_stacks_empty:
  forall stk stk' bound,
  match_stacks F m m' L L' stk stk' bound -> stk = nil -> stk' = nil
with match_stacks_inside_empty:
  forall stk stk' f ctx sp rs,
  match_stacks_inside F m m' L L' stk stk' f ctx sp rs -> stk = nil -> stk' = nil /\ ctx.(retinfo) = None.
Proof.
  induction 1; intros.
  auto.
  discriminate.
  exploit match_stacks_inside_empty; eauto. intros [A B]. congruence.
  induction 1; intros.
  split. eapply match_stacks_empty; eauto. auto.
  discriminate.
Qed.

End MATCH_STACKS.

(** Preservation by assignment to a register *)

Lemma match_stacks_inside_set_reg:
  forall F m m' L L' stk stk' f' ctx sp' rs' r v,
  match_stacks_inside F m m' L L' stk stk' f' ctx sp' rs' ->
  match_stacks_inside F m m' L L' stk stk' f' ctx sp' (rs'#(sreg ctx r) <- v).
Proof.
  intros. eapply match_stacks_inside_invariant; eauto.
  intros. apply Regmap.gso. zify. unfold sreg; rewrite shiftpos_eq. xomega.
Qed.

Lemma match_stacks_inside_set_res:
  forall F m m' L L' stk stk' f' ctx sp' rs' res v,
  match_stacks_inside F m m' L L' stk stk' f' ctx sp' rs' ->
  match_stacks_inside F m m' L L' stk stk' f' ctx sp' (regmap_setres (sbuiltinres ctx res) v rs').
Proof.
  intros. destruct res; simpl; auto.
  apply match_stacks_inside_set_reg; auto.
Qed.

(** Preservation by a memory store *)

Lemma match_stacks_inside_store:
  forall F m m' L L' stk stk' f' ctx sp' rs' chunk b ofs v m1 chunk' b' ofs' v' m1',
  match_stacks_inside F m m' L L' stk stk' f' ctx sp' rs' ->
  Mem.store chunk m b ofs v = Some m1 ->
  Mem.store chunk' m' b' ofs' v' = Some m1' ->
  match_stacks_inside F m1 m1' L L' stk stk' f' ctx sp' rs'.
Proof.
  intros.
  eapply match_stacks_inside_invariant with (m':=m'); eauto with mem.
Qed.

(** Preservation by an allocation *)

Lemma match_stacks_inside_alloc_left:
  forall F m m' L L' stk stk' f' ctx sp' rs',
  match_stacks_inside F m m' L L' stk stk' f' ctx sp' rs' ->
  forall sz m1 b F1 delta,
  Mem.alloc m 0 sz = (m1, b) ->
  inject_incr F F1 ->
  F1 b = Some(sp', delta) ->
  (forall b1, b1 <> b -> F1 b1 = F b1) ->
  delta >= ctx.(dstk) ->
  match_stacks_inside F1 m1 m' L L' stk stk' f' ctx sp' rs'.
Proof.
  induction 1; intros.
  (* base *)
  eapply match_stacks_inside_base; eauto.
  eapply match_stacks_invariant; eauto.
  intros. destruct (eq_block b1 b).
  subst b1. rewrite H1 in H4; inv H4. eelim Plt_strict; eauto.
  rewrite H2 in H4; auto.
  intros. exploit Mem.perm_alloc_inv; eauto. destruct (eq_block b1 b); intros; auto.
  subst b1. rewrite H1 in H4. inv H4. eelim Plt_strict; eauto.
  (* inlined *)
  eapply match_stacks_inside_inlined; eauto.
  eapply IHmatch_stacks_inside; eauto. destruct SBELOW. omega.
  eapply agree_regs_incr; eauto.
  eapply range_private_invariant; eauto.
  intros. exploit Mem.perm_alloc_inv; eauto. destruct (eq_block b0 b); intros.
  subst b0. rewrite H2 in H5; inv H5. elimtype False; xomega.
  rewrite H3 in H5; auto.
Qed.

(** Preservation by freeing *)

Lemma match_stacks_free_left:
  forall F m m' L L' stk stk' sp b lo hi m1,
  match_stacks F m m' L L' stk stk' sp ->
  Mem.free m b lo hi = Some m1 ->
  match_stacks F m1 m' L L' stk stk' sp.
Proof.
  intros. eapply match_stacks_invariant; eauto.
  intros. eapply Mem.perm_free_3; eauto.
Qed.

Lemma match_stacks_free_right:
  forall F m m' L L' stk stk' sp lo hi m1',
  match_stacks F m m' L L' stk stk' sp ->
  Mem.free m' sp lo hi = Some m1' ->
  match_stacks F m m1' L L' stk stk' sp.
Proof.
  intros. specialize (Mem.valid_block_free_1 _ _ _ _ _ H0); intros.
  eapply match_stacks_invariant; eauto.
  intros. eapply Mem.perm_free_1; eauto.
  intros. eapply Mem.perm_free_3; eauto.
Qed.

Lemma min_alignment_sound:
  forall sz n, (min_alignment sz | n) -> Mem.inj_offset_aligned n sz.
Proof.
  intros; red; intros. unfold min_alignment in H.
  assert (2 <= sz -> (2 | n)). intros.
    destruct (zle sz 1). omegaContradiction.
    destruct (zle sz 2). auto.
    destruct (zle sz 4). apply Zdivides_trans with 4; auto. exists 2; auto.
    apply Zdivides_trans with 8; auto. exists 4; auto.
  assert (4 <= sz -> (4 | n)). intros.
    destruct (zle sz 1). omegaContradiction.
    destruct (zle sz 2). omegaContradiction.
    destruct (zle sz 4). auto.
    apply Zdivides_trans with 8; auto. exists 2; auto.
  assert (8 <= sz -> (8 | n)). intros.
    destruct (zle sz 1). omegaContradiction.
    destruct (zle sz 2). omegaContradiction.
    destruct (zle sz 4). omegaContradiction.
    auto.
  destruct chunk; simpl in *; auto.
  apply Zone_divide.
  apply Zone_divide.
  apply H2; omega.
  apply H2; omega.
Qed.

(** Preservation by external calls *)
(*
Section EF_CALL.
(*COMPCOMP: we have two versions of the match_stacks_extcall-lemmas:
  EF-versions have the same Hypothesis SEP as in original compcert but are now only
  applicable to EF-externals.

  Truly external calls (transitioning from atExt to AfterExt) have Hypothesis GSEP,
  and assumptions mini_extern_incr (see the enxt section).
  This distinction is necessary to correctly classify blocks that are allocated 
  during an EF-external (ie builtins, in fact only EF_malloc allocates at all)
  as local blocks, and blocks allocated by other cores as non-local.*)
Variables F1 F2: meminj.
Variables m1 m2 m1' m2': mem.
Hypothesis MAXPERM: forall b ofs p, Mem.valid_block m1 b -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p.
Hypothesis MAXPERM': forall b ofs p, Mem.valid_block m1' b -> Mem.perm m2' b ofs Max p -> Mem.perm m1' b ofs Max p.

Variables (L L': block -> bool).
Hypothesis UNCHANGED: Mem.unchanged_on (o_o_reach F1 L' m1) m1' m2'. 

Hypothesis INJ: Mem.inject F1 m1 m1'.

Hypothesis INCR: inject_incr F1 F2.
Hypothesis SEP: inject_separated F1 F2 m1 m1'. 
Hypothesis VB': forall b', Mem.valid_block m1' b' -> Mem.valid_block m2' b'.

Lemma match_stacks_EF_call:
  forall stk stk' bound,
  match_stacks F1 m1 m1' L L' stk stk' bound ->
  Ple bound (Mem.nextblock m1') ->
  match_stacks F2 m2 m2' L L' stk stk' bound
with match_stacks_inside_EF_call:
  forall stk stk' f' ctx sp' rs',
  match_stacks_inside F1 m1 m1' L L' stk stk' f' ctx sp' rs' ->
  Plt sp' (Mem.nextblock m1') ->
  L' sp' = true ->
  match_stacks_inside F2 m2 m2' L L' stk stk' f' ctx sp' rs'.
Proof.
  induction 1; intros.
  apply match_stacks_nil with bound1; auto.
    inv MG. constructor; intros; eauto.
    destruct (F1 b1) as [[b2' delta']|] eqn:?.
    exploit INCR; eauto. intros EQ; rewrite H0 in EQ; inv EQ. eapply IMAGE; eauto.
    exploit SEP; eauto. intros [A B]. elim B. red. xomega.
    intros. destruct (EXT _ H0). split; eauto. 
  eapply match_stacks_cons; eauto.
    eapply match_stacks_inside_EF_call; eauto. xomega.
    eapply agree_regs_incr; eauto.
    eapply range_private_extcall; eauto. intros. intros N; subst. destruct (SEP _ _ _ H0 H1). elim H3. unfold Mem.valid_block; xomega.
    red; xomega.
    intros. apply SSZ2; auto. apply MAXPERM'; auto. red; xomega.
  eapply match_stacks_untailcall; eauto.
    eapply match_stacks_inside_EF_call; eauto. xomega.
    eapply range_private_extcall; eauto. intros. intros N; subst. destruct (SEP _ _ _ H0 H1). elim H3. unfold Mem.valid_block; xomega.
    red; xomega.
    intros. apply SSZ2; auto. apply MAXPERM'; auto. red; xomega.
  induction 1; intros.
  eapply match_stacks_inside_base; eauto.
    eapply match_stacks_EF_call; eauto. xomega.
  eapply match_stacks_inside_inlined; eauto.
    eapply agree_regs_incr; eauto.
    eapply range_private_extcall; eauto. intros. intros N; subst. destruct (SEP _ _ _ H2 H3). elim H5. unfold Mem.valid_block; xomega.
Qed.

End EF_CALL.
*)
Section EXTCALL.

Variables F1 F2: meminj.
Variables m1 m2 m1' m2': mem.
Hypothesis MAXPERM: forall b ofs p, Mem.valid_block m1 b -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p.
Hypothesis MAXPERM': forall b ofs p, Mem.valid_block m1' b -> Mem.perm m2' b ofs Max p -> Mem.perm m1' b ofs Max p.

Variables (L L': block -> bool).
Hypothesis UNCHANGED: Mem.unchanged_on (o_o_reach F1 L' m1) m1' m2'. 

Hypothesis INJ: Mem.inject F1 m1 m1'.
Hypothesis GSEP: globals_separate m1 tge F1 F2.

Hypothesis VB': forall b', Mem.valid_block m1' b' -> Mem.valid_block m2' b'.

Lemma match_stacks_extcall:
  forall stk stk' bound,
  match_stacks F1 m1 m1' L L' stk stk' bound ->
  Ple bound (Mem.nextblock m1') ->
  mini_extern_incr F1 F2 L L' ->
  match_stacks F2 m2 m2' L L' stk stk' bound
with match_stacks_inside_extcall:
  forall stk stk' f' ctx sp' rs',
  match_stacks_inside F1 m1 m1' L L' stk stk' f' ctx sp' rs' ->
  mini_extern_incr F1 F2 L L' ->
  Plt sp' (Mem.nextblock m1') ->
  L' sp' = true ->
  match_stacks_inside F2 m2 m2' L L' stk stk' f' ctx sp' rs'.
Proof.
- induction 1; intros.
* destruct H0 as [INCR SEP].
  apply match_stacks_nil with bound1; auto.
  + inv MG. constructor; intros; eauto.
    destruct (F1 b1) as [[b2' delta']|] eqn:?.
    exploit INCR; eauto. intros EQ; rewrite H0 in EQ; inv EQ. eapply IMAGE; eauto.
    specialize (GLOBbnd _ H1). 
    exploit GSEP; eauto. (* congruence. *) intros [A B]; xomega.
  + intros. destruct (EXT _ H0). split; eauto. 
* eapply match_stacks_cons; eauto.
  + eapply match_stacks_inside_extcall; eauto. xomega.
  + destruct H0 as [INCR SEP].
    eapply agree_regs_incr; eauto.
  + destruct H0 as [INCR SEP]. eapply INCR; trivial.
  + destruct H0 as [INCR SEP].
    eapply range_private_extcall; eauto. intros. intros N; subst. destruct (SEP _ _ _ H0 H1). congruence. 
    red; xomega.
  + intros. apply SSZ2; auto. apply MAXPERM'; auto. red; xomega.
* eapply match_stacks_untailcall; eauto.
  + eapply match_stacks_inside_extcall; eauto. xomega.
  + destruct H0 as [INCR SEP].
    eapply range_private_extcall; eauto. intros. intros N; subst. destruct (SEP _ _ _ H0 H1). congruence. 
    red; xomega.
  + intros. apply SSZ2; auto. apply MAXPERM'; auto. red; xomega.
- induction 1; intros.
  * eapply match_stacks_inside_base; eauto.
    eapply match_stacks_extcall; eauto. xomega.
  * specialize (IHmatch_stacks_inside H0).
    destruct H0 as [INCR SEP].
    eapply match_stacks_inside_inlined; eauto.
    eapply agree_regs_incr; eauto.
    eapply range_private_extcall; eauto. intros. intros N; subst. destruct (SEP _ _ _ H0 H3). congruence. 
Qed.

End EXTCALL.

(** Change of context corresponding to an inlined tailcall *)

Lemma align_unchanged:
  forall n amount, amount > 0 -> (amount | n) -> align n amount = n.
Proof.
  intros. destruct H0 as [p EQ]. subst n. unfold align. decEq.
  apply Zdiv_unique with (b := amount - 1). omega. omega.
Qed.

Lemma match_stacks_inside_inlined_tailcall:
  forall fenv F m m' L L' stk stk' f' ctx sp' rs' ctx' f,
  match_stacks_inside F m m' L L' stk stk' f' ctx sp' rs' ->
  context_below ctx ctx' ->
  context_stack_tailcall ctx f ctx' ->
  ctx'.(retinfo) = ctx.(retinfo) ->
  range_private L' F m m' sp' ctx.(dstk) f'.(fn_stacksize) ->
  tr_funbody fenv f'.(fn_stacksize) ctx' f f'.(fn_code) ->
  match_stacks_inside F m m' L L' stk stk' f' ctx' sp' rs'.
Proof.
  intros. inv H.
  (* base *)
  eapply match_stacks_inside_base; eauto. congruence.
  rewrite H1. rewrite DSTK. apply align_unchanged. apply min_alignment_pos. apply Zdivide_0.
  (* inlined *)
  assert (dstk ctx <= dstk ctx'). rewrite H1. apply align_le. apply min_alignment_pos.
  eapply match_stacks_inside_inlined; eauto.
  split; trivial; intros. destruct (zlt ofs (dstk ctx)). apply PAD; omega. apply H3. inv H4. xomega.
  congruence.
  unfold context_below in *. xomega.
  unfold context_stack_call in *. omega.
Qed.

(** ** Relating states *)
(*CompComp adaptation: old type: Inductive match_states: RTL.state -> RTL.state -> Prop :=...*)
Inductive match_states (L L': block -> bool) (F:meminj): RTL_memsem.state -> mem -> RTL_memsem.state -> mem -> Prop :=
  | match_regular_states: forall stk f sp pc rs m stk' f' sp' rs' m' fenv ctx
        (MS: match_stacks_inside F m m' L L' stk stk' f' ctx sp' rs')
        (COMPAT: fenv_compat prog fenv)
        (FB: tr_funbody fenv f'.(fn_stacksize) ctx f f'.(fn_code))
        (AG: agree_regs F ctx rs rs')
        (SP: F sp = Some(sp', ctx.(dstk)))
        (MINJ: Mem.inject F m m')
        (VBsp': Mem.valid_block m' sp') (*COMPCOMP comment: clause follows from MINJ and SP, even in original compcert*)
        (PRIV: range_private L' F m m' sp' (ctx.(dstk) + ctx.(mstk)) f'.(fn_stacksize))
        (SSZ1: 0 <= f'.(fn_stacksize) < Int.max_unsigned)
        (SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs <= f'.(fn_stacksize))
        (Lsp: L sp = true)
        (Lsp': L' sp' = true),
      match_states L L' F (State stk f (Vptr sp Int.zero) pc rs) m
                        (State stk' f' (Vptr sp' Int.zero) (spc ctx pc) rs') m'
  | match_call_states: forall stk fd args m stk' fd' args' m' cunit 
        (MS: match_stacks F m m' L L' stk stk' (Mem.nextblock m'))
        (LINK: linkorder cunit prog)
        (FD: transf_fundef (funenv_program cunit) fd = OK fd')
        (VINJ: Val.inject_list F args args')
        (MINJ: Mem.inject F m m'),
      match_states L L' F (Callstate stk fd args) m
                        (Callstate stk' fd' args') m'
  | match_call_regular_states: forall stk f vargs m stk' f' sp' rs' m' fenv ctx ctx' pc' pc1' rargs
        (MS: match_stacks_inside F m m' L L' stk stk' f' ctx sp' rs')
        (COMPAT: fenv_compat prog fenv)
        (FB: tr_funbody fenv f'.(fn_stacksize) ctx f f'.(fn_code))
        (BELOW: context_below ctx' ctx)
        (NOP: f'.(fn_code)!pc' = Some(Inop pc1'))
        (MOVES: tr_moves f'.(fn_code) pc1' (sregs ctx' rargs) (sregs ctx f.(fn_params)) (spc ctx f.(fn_entrypoint)))
        (VINJ: list_forall2 (val_reg_charact F ctx' rs') vargs rargs)
        (MINJ: Mem.inject F m m')
        (VBsp': Mem.valid_block m' sp')
        (PRIV: range_private L' F m m' sp' ctx.(dstk) f'.(fn_stacksize))
        (SSZ1: 0 <= f'.(fn_stacksize) < Int.max_unsigned)
        (SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs <= f'.(fn_stacksize))
        (Lsp': L' sp' = true),
      match_states L  L' F (Callstate stk (Internal f) vargs) m
                         (State stk' f' (Vptr sp' Int.zero) pc' rs') m'
  | match_return_states: forall stk v m stk' v' m'
        (MS: match_stacks F m m' L L' stk stk' (Mem.nextblock m'))
        (VINJ: Val.inject F v v')
        (MINJ: Mem.inject F m m'),
      match_states L L' F (Returnstate stk v) m
                        (Returnstate stk' v') m'
  | match_return_regular_states: forall stk v m stk' f' sp' rs' m' ctx pc' or rinfo
        (MS: match_stacks_inside F m m' L L' stk stk' f' ctx sp' rs')
        (RET: ctx.(retinfo) = Some rinfo)
        (AT: f'.(fn_code)!pc' = Some(inline_return ctx or rinfo))
        (VINJ: match or with None => v = Vundef | Some r => Val.inject F v rs'#(sreg ctx r) end)
        (MINJ: Mem.inject F m m')
        (VBsp': Mem.valid_block m' sp')
        (PRIV: range_private L' F m m' sp' ctx.(dstk) f'.(fn_stacksize))
        (SSZ1: 0 <= f'.(fn_stacksize) < Int.max_unsigned)
        (SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs <= f'.(fn_stacksize))
        (Lsp': L' sp' = true),
      match_states L L' F (Returnstate stk v) m
                        (State stk' f' (Vptr sp' Int.zero) pc' rs') m'.

(** ** Forward simulation *)

Definition measure (S: RTL_memsem.state) : nat :=
  match S with
  | State _ _ _ _ _ (*_*) => 1%nat
  | Callstate _ _ _ (*_*) => 0%nat
  | Returnstate _ _ (*_*) => 0%nat
  end.

Lemma tr_funbody_inv:
  forall fenv sz cts f c pc i,
  tr_funbody fenv sz cts f c -> f.(fn_code)!pc = Some i -> tr_instr fenv sz cts pc i c.
Proof.
  intros. inv H. eauto.
Qed.

Lemma match_stacks_sub:
  forall F m m' L L' stk stk' bound, match_stacks F m m' L L' stk stk' bound ->
  forall K (HK: forall b, L b = true -> K b = true)
         K' (HK': forall b, L' b = true -> K' b = true)
         (*(Glob': forall b' : block, isGlobalBlock tge b' = true -> K' b' = false)*)
         (Glob': forall b', Plt b' (Genv.genv_next tge) -> K' b' = false),
  match_stacks F m m' K K' stk stk' bound

with match_stacks_inside_sub:
  forall F m m' L L' stk stk' f' ctx sp' rs,
  match_stacks_inside F m m' L L' stk stk' f' ctx sp' rs ->
  forall K (HK: forall b, L b = true -> K b = true)
         K' (HK': forall b, L' b = true -> K' b = true)
         (*(Glob': forall b' : block, isGlobalBlock tge b' = true -> K' b' = false)*)
         (Glob': forall b', Plt b' (Genv.genv_next tge) -> K' b' = false),
  match_stacks_inside F m m' K K' stk stk' f' ctx sp' rs.
Proof.
+ induction 1; intros.
- (* nil *)
  apply match_stacks_nil with (bound1 := bound1); trivial.
  intros. destruct (EXT _ H); split; auto. 
- (* cons *)
  apply match_stacks_cons with (fenv := fenv) (ctx := ctx); auto.
  eapply match_stacks_inside_sub; eauto.
  destruct PRIV.
  split; eauto. 
- (* untailcall *)
  apply match_stacks_untailcall with (ctx := ctx); auto.
  eapply match_stacks_inside_sub; eauto.
  destruct PRIV.
  split; eauto. 
+ induction 1; intros.
- (* base *)
  eapply match_stacks_inside_base; eauto.
- (* inlined *)
  apply match_stacks_inside_inlined with (fenv := fenv) (ctx' := ctx'); auto.
  destruct PAD.
  split; eauto. 
Qed.

Lemma match_stacks_globals_not_local:
  forall F m m' L L' stk stk' bound, match_stacks F m m' L L' stk stk' bound ->
  (*forall b' : block, isGlobalBlock tge b' = true -> L' b' = false /\ Mem.valid_block m' b'*)
   forall b', Plt b' (Genv.genv_next tge) -> L' b' = false /\ Mem.valid_block m' b'
with match_stacks_inside_globals_not_local:
  forall F m m' L L' stk stk' f' ctx sp' rs,
  match_stacks_inside F m m' L L' stk stk' f' ctx sp' rs ->
  (*forall b' : block, isGlobalBlock tge b' = true -> L' b' = false /\ Mem.valid_block m' b'.*)
   forall b', Plt b' (Genv.genv_next tge) -> L' b' = false /\ Mem.valid_block m' b'.
Proof.
+ induction 1; eauto.
+ induction 1; eauto. 
Qed.

Definition core_data:Type := RTL_memsem.state.

Definition match_cores (cd:core_data) (j:meminj) (L:block -> bool) (st:RTL_memsem.state) (m:mem) (L':block -> bool) (st':RTL_memsem.state) (m':mem) : Prop :=
  cd=st /\ match_states L L' j st m st' m' /\ 
 (forall b, L b = true -> Mem.valid_block m b) /\ (forall b, L' b = true -> Mem.valid_block m' b) /\
 (forall b b' d, j b = Some(b',d) -> L b = L' b') /\
 (Ple (Genv.genv_next ge) (Mem.nextblock m)) /\
 (Ple (Genv.genv_next tge) (Mem.nextblock m')) /\ symbols_inject j ge tge.

Lemma match_cores_inject d j L1 c1 m1 L2 c2 m2 (MC: match_cores d j L1 c1 m1 L2 c2 m2):
      Mem.inject j m1 m2.
Proof. destruct MC as [? [MC [HL HL']]]. subst.
  inv MC; trivial.
Qed.

Lemma match_cores_loc_valid_left d j L1 c1 m1 L2 c2 m2 (MC: match_cores d j L1 c1 m1 L2 c2 m2)
      b (Hb: L1 b = true): Mem.valid_block m1 b.
Proof. eapply MC; eassumption. Qed.

Lemma match_cores_loc_valid_right d j L1 c1 m1 L2 c2 m2 (MC: match_cores d j L1 c1 m1 L2 c2 m2)
      b (Hb: L2 b = true): Mem.valid_block m2 b.
Proof. eapply MC; eassumption. Qed.

Lemma match_cores_glob_valid_left d j L1 c1 m1 L2 c2 m2 (MC: match_cores d j L1 c1 m1 L2 c2 m2)
      b (Hb: Plt b (Genv.genv_next ge)): Mem.valid_block m1 b.
Proof. destruct MC as [MS [? [? [? [? [? ?]]]]]]; unfold Mem.valid_block; xomega. Qed. 

Lemma match_cores_glob_valid_right d j L1 c1 m1 L2 c2 m2 (MC: match_cores d j L1 c1 m1 L2 c2 m2)
      b (Hb: Plt b (Genv.genv_next tge)): Mem.valid_block m2 b.
Proof. destruct MC as [MS [? [? [? [? [? ?]]]]]]; unfold Mem.valid_block; xomega. Qed. 


Lemma core_diagram: forall (st1 : RTL_memsem.state) (m1 : mem) 
                           (st1' : RTL_memsem.state) (m1' : mem) (U1 : block -> Z -> bool)
      (STEP: effstep RTL_eff_sem ge U1 st1 m1 st1' m1')
      (st2 : RTL_memsem.state) (j : meminj) (m2 : mem)
      (L1 L2 : block -> bool)
      (MC: match_cores st1 j L1 st1 m1 L2 st2 m2),
exists
  (st2' : RTL_memsem.state) (m2' : mem) (j' : meminj) (L1' L2' : block -> bool),
  mini_intern_incr j j' L1' L2' /\
  globals_separate m1 tge j j' /\
  mini_locally_allocated L1 L2 m1 m2 L1' L2' m1' m2' /\
  match_cores st1' j' L1' st1' m1' L2' st2' m2' /\
  (exists U2 : block -> Z -> bool,
     (effstep_plus RTL_eff_sem tge U2 st2 m2 st2' m2' \/
      (measure st1' < measure st1)%nat /\
      effstep_star RTL_eff_sem tge U2 st2 m2 st2' m2') /\
     ((forall (b1 : block) (z : Z),
       U1 b1 z = true -> L1 b1 = true \/ j b1 <> None) ->
      forall (b2 : block) (ofs : Z),
      U2 b2 ofs = true ->
      L2 b2 = true \/
      (exists (b1 : block) (delta : Z),
         j b1 = Some (b2, delta) /\ U1 b1 (ofs - delta) = true))).
Proof.
  specialize mini_intern_incr_same_meminj; intros INC_SAME.
  (*specialize (globals_separate_same_meminj ge tge); intros GSEP_SAME.*)
  specialize mini_locally_allocated_same; intros LOCALLOC_SAME.
  induction 1; intros; destruct MC as [_ [MS [HL1 [HL2 [HLL [GV1 [GV2 SINJ]]]]]]]; inv MS;
  specialize (globals_separate_same_meminj m tge); intros GSEP_SAME. 

- (* nop *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  exists (State stk' f' (Vptr sp' Int.zero) (spc ctx pc') rs'), m2, j, L1, L2. 
  intuition.
  + split; trivial. 
    intuition. econstructor; eauto. 
  + eexists; split. left. apply effstep_plus_one.
    eapply effexec_Inop; eauto.
    intros HH bb ofs EFF; inv EFF.

- (* op *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  exploit eval_operation_inject.
    eapply match_stacks_inside_globals; eauto.
    eexact SP.
    instantiate (2 := rs##args). instantiate (1 := rs'##(sregs ctx args)). eapply agree_val_regs; eauto.
    eexact MINJ. eauto.
  fold (sop ctx op). intros [v' [A B]].
  exists (State stk' f' (Vptr sp' Int.zero) (spc ctx pc') rs' # (sreg ctx res) <- v'), m2, j, L1, L2. 
  intuition.
  + split; trivial. 
    intuition. econstructor; eauto.
    apply match_stacks_inside_set_reg; auto.
    apply agree_set_reg; auto.
  + eexists; split. left. apply effstep_plus_one. 
    eapply effexec_Iop; eauto. erewrite eval_operation_preserved; eauto.
    exact symbols_preserved.
    intros HH bb ofs EFF; inv EFF. 

- (* load *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  exploit eval_addressing_inject.
    eapply match_stacks_inside_globals; eauto.
    eexact SP.
    instantiate (2 := rs##args). instantiate (1 := rs'##(sregs ctx args)). eapply agree_val_regs; eauto.
    eauto.
  fold (saddr ctx addr). intros [a' [P Q]].
  exploit Mem.loadv_inject; eauto. intros [v' [U V]].
  assert (eval_addressing tge (Vptr sp' Int.zero) (saddr ctx addr) rs' ## (sregs ctx args) = Some a').
  rewrite <- P. apply eval_addressing_preserved. exact symbols_preserved.
  exists (State stk' f' (Vptr sp' Int.zero) (spc ctx pc') rs' # (sreg ctx dst) <- v'), m2, j, L1, L2. 
  intuition.
  + split; trivial.
    intuition. econstructor; eauto.
    apply match_stacks_inside_set_reg; auto.
    apply agree_set_reg; auto.
  + eexists; split. left. apply effstep_plus_one. 
    eapply effexec_Iload; eauto.
    intros HH bb ofs EFF; inv EFF. 

- (* store *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  exploit eval_addressing_inject.
    eapply match_stacks_inside_globals; eauto.
    eexact SP.
    instantiate (2 := rs##args). instantiate (1 := rs'##(sregs ctx args)). eapply agree_val_regs; eauto.
    eauto.
  fold saddr. intros [a' [P Q]].
  exploit Mem.storev_mapped_inject; eauto. eapply agree_val_reg; eauto.
  intros [m2' [U V]].
  assert (eval_addressing tge (Vptr sp' Int.zero) (saddr ctx addr) rs' ## (sregs ctx args) = Some a').
    rewrite <- P. apply eval_addressing_preserved. exact symbols_preserved.
  exists (State stk' f' (Vptr sp' Int.zero) (spc ctx pc') rs'), m2', j, L1, L2.
  intuition.
  + eapply mini_locally_allocated_storev; eassumption. 
  + destruct a; simpl in H1; try discriminate.
    destruct a'; simpl in U; try discriminate.
    assert (FWD2:= Mem.store_valid_block_1 _ _ _ _ _ _ U).
    assert (FWD:= Mem.store_valid_block_1 _ _ _ _ _ _ H1).
    split; trivial. intuition.
    * econstructor; eauto.
      eapply match_stacks_inside_store; eauto.
      eapply range_private_invariant; eauto.
      intros; split; auto. eapply Mem.perm_store_2; eauto.
      intros; eapply Mem.perm_store_1; eauto.
      intros. eapply SSZ2. eapply Mem.perm_store_2; eauto.
    * eapply Ple_trans. apply GV1. apply forward_nextblock. eapply store_forward; eassumption.
    * eapply Ple_trans. apply GV2. apply forward_nextblock. eapply store_forward; eassumption.
  + eexists; split. left. apply effstep_plus_one. 
    eapply effexec_Istore; eauto.
    rename U into ST2. rename H1 into ST1.
    intros HH bb ofs EFF. 
      apply StoreEffectD in EFF. destruct EFF as [i [VADDR' Hoff]]. subst.
      destruct a; inv ST1. rename H5 into ST1. inv Q. 
      remember (L2 bb) as q; symmetry in Heqq; destruct q. left; trivial. right.
      eapply StoreEffect_propagate_inj; eassumption.
- (* call *)
  exploit match_stacks_inside_globalenvs; eauto. intros [bound G].
  exploit find_function_agree; eauto. intros (cu & fd' & A & B & C).
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
+ (* not inlined *)
  exists (Callstate
     (Stackframe (sreg ctx res) f' (Vptr sp' Int.zero) (spc ctx pc') rs' :: stk') fd'
     rs' ## (sregs ctx args)).
  exists m2, j, L1, L2.
  intuition.
  * split; trivial.
    intuition.
    econstructor; eauto.
    eapply match_stacks_cons; eauto.
    eapply agree_val_regs; eauto.
  * eexists; split. left. apply effstep_plus_one. 
    eapply effexec_Icall; eauto.
    eapply sig_function_translated; eauto.
    intros HH bb ofs EFF; inv EFF. 
+ (* inlined *)
  assert (EQ: fd = Internal f0) by (eapply find_inlined_function; eauto).
  subst fd.
  exists (State stk' f' (Vptr sp' Int.zero) (spc ctx pc) rs').
  exists m2, j, L1, L2.
  intuition. 
  * split; trivial. intuition. 
    econstructor; eauto.
    eapply match_stacks_inside_inlined; eauto.
    split; trivial; intros. apply PRIV. inv H13. destruct H16. xomega.
    apply agree_val_regs_gen; auto.
    split; trivial; intros; apply PRIV. destruct H16. omega.
  * eexists. split.
    right; split. simpl; omega.
    apply effstep_star_zero.
    intros HH bb ofs EFF; inv EFF. 

- (* tailcall *)
  exploit match_stacks_inside_globalenvs; eauto. intros [bound G].
  exploit find_function_agree; eauto. intros (cu & fd' & A & B & C).
  assert (PRIV': range_private L2 j m' m2 sp' (dstk ctx) f'.(fn_stacksize)).
  { eapply range_private_free_left; eauto. inv FB. rewrite <- H4. auto. }
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
+ (* within the original function *)
  inv MS0; try congruence.
  assert (X: { m2' | Mem.free m2 sp' 0 (fn_stacksize f') = Some m2'}).
    apply Mem.range_perm_free. red; intros.
    destruct (zlt ofs f.(fn_stacksize)).
    replace ofs with (ofs + dstk ctx) by omega. eapply Mem.perm_inject; eauto.
    eapply Mem.free_range_perm; eauto. omega.
    inv FB. eapply range_private_perms; eauto. xomega.
  destruct X as [m2' FREE].
  specialize ( Mem.valid_block_free_1 _ _ _ _ _ H2); intros VB.
  specialize ( Mem.valid_block_free_1 _ _ _ _ _ FREE); intros VB'.
  exists (Callstate stk' fd' rs' ## (sregs ctx args)), m2', j, L1, L2.
  intuition.
  * red. erewrite freshblock_free; try eassumption. erewrite freshblock_free; try eassumption. 
    do 2 rewrite orb_false_r_ext. split; trivial.
  * split; trivial. intuition.
    econstructor; eauto.
       eapply match_stacks_bound with (bound := sp').
       eapply match_stacks_invariant; eauto.
         intros. eapply Mem.perm_free_3; eauto.
         intros. eapply Mem.perm_free_1; eauto.
         intros. eapply Mem.perm_free_3; eauto.
       erewrite Mem.nextblock_free; eauto. red in VBsp'; xomega.
       eapply agree_val_regs; eauto.
       eapply Mem.free_right_inject; eauto. eapply Mem.free_left_inject; eauto.
       (* show that no valid location points into the stack block being freed *)
       intros. rewrite DSTK in PRIV'. destruct PRIV' as [L2sp' PRIV']. exploit (PRIV' (ofs + delta)). omega. intros [P Q].
       eelim Q; eauto. replace (ofs + delta - delta) with ofs by omega.
       apply Mem.perm_max with k. apply Mem.perm_implies with p; auto with mem.
    eapply Ple_trans. apply GV1. eapply forward_nextblock. eapply free_forward; eassumption. 
    eapply Ple_trans. apply GV2. eapply forward_nextblock. eapply free_forward; eassumption. 
 * eexists. split. left. apply effstep_plus_one. 
    eapply effexec_Itailcall; eauto.
    eapply sig_function_translated; eauto.
    intros HH bb ofs EFF. 
    apply FreeEffectD in EFF. destruct EFF as [? [VBsp'' BND]]; subst bb. left; trivial.

+ (* turned into a call *)
  exists (Callstate (Stackframe res f' (Vptr sp' Int.zero) s0 rs' :: stk') fd'
     rs' ## (sregs ctx args)); exists m2, j, L1, L2.
  intuition.
  * red. erewrite freshblock_free; try eassumption. rewrite fresh_no_alloc.
    rewrite orb_false_r_ext. split; trivial.
  * split; trivial. intuition.
    ++ econstructor; eauto.
       eapply match_stacks_untailcall; eauto.
       eapply match_stacks_inside_invariant; eauto.
         intros. eapply Mem.perm_free_3; eauto.
       eapply agree_val_regs; eauto.
       eapply Mem.free_left_inject; eauto.
    ++ eapply Mem.valid_block_free_1; eauto.
    ++ eapply Ple_trans; eauto. apply forward_nextblock. eapply free_forward; eauto.
  * eexists. split. left. apply effstep_plus_one. 
    eapply effexec_Icall; eauto.
    eapply sig_function_translated; eauto.
    intros HH bb ofs EFF; inv EFF.

+ (* inlined *)
  assert (EQ: fd = Internal f0) by (eapply find_inlined_function; eauto).
  subst fd.
  exists  (State stk' f' (Vptr sp' Int.zero) (spc ctx pc) rs'), m2, j, L1, L2.
  intuition.
  * red. erewrite freshblock_free; try eassumption. rewrite fresh_no_alloc.
    rewrite orb_false_r_ext. split; trivial.
  * split; trivial. intuition.
    ++ econstructor; eauto.
       eapply match_stacks_inside_inlined_tailcall; eauto.
       eapply match_stacks_inside_invariant; eauto.
         intros. eapply Mem.perm_free_3; eauto.
       apply agree_val_regs_gen; auto.
       eapply Mem.free_left_inject; eauto.
       destruct PRIV' as [L2sp' PRIV']. split; trivial; intros; apply PRIV'.
         assert (dstk ctx <= dstk ctx'). red in H14; rewrite H14. apply align_le. apply min_alignment_pos.
         omega.
    ++ eapply Mem.valid_block_free_1; eauto.
    ++ eapply Ple_trans; eauto. apply forward_nextblock. eapply free_forward; eauto.
  * eexists. split. right. split; simpl. omega. apply effstep_star_zero.
    intros HH bb ofs EFF; inv EFF.
- (* builtin *) 
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  exploit match_stacks_inside_globalenvs; eauto. intros [bound MG].
  exploit tr_builtin_args; eauto. intros (vargs' & P & Q).
  
  exploit (nonobservables_mem_inject ge tge); try eassumption.
  { eapply match_globalenvs_preserves_globals; eauto. }
  intros [j' [v1 [m2' [A [B [C [D [E [INC SEP]]]]]]]]].
  assert (FwdSrc: mem_forward m m') by (eapply external_call_mem_forward; eauto).
  assert (FwdTgt: mem_forward m2 m2') by (eapply external_call_mem_forward; eauto).
  eexists (State stk' f' (Vptr sp' Int.zero) (spc ctx pc')
     (regmap_setres (sbuiltinres ctx res) v1 rs')). 
  exists m2', j'.
  exists (fun b => L1 b || freshblock m m' b), (fun b => L2 b || freshblock m2 m2' b).
  intuition.
  * split; trivial; intros.
    destruct (SEP _ _ _ J J') as [vb vb'].
    assert (Fb: freshblock m m' b1 = true). { apply freshblockProp_char. split; trivial. eapply Mem.valid_block_inject_1; eauto. }
    assert (Fb': freshblock m2 m2' b2 = true). { apply freshblockProp_char. split; trivial. eapply Mem.valid_block_inject_2; eauto. }
    rewrite Fb, Fb'. split; apply orb_true_r.
  * red; intros. destruct (SEP _ _ _ J J').
    destruct (Plt_Ple_dec b2 (Genv.genv_next tge)).
    ++ exploit match_stacks_inside_globals_not_local. apply MS0. apply p. intros [AA BB]; contradiction.
    ++ split; trivial. (* destruct (Plt_Ple_dec b1 (Genv.genv_next ge)); trivial.
       elim H5. unfold Mem.valid_block. xomega. *)
  * split; trivial.
  * split; trivial. intuition.
    ++ econstructor.
       eapply match_stacks_inside_set_res.
       -- eapply match_stacks_inside_sub with (L:=L1). 2: intros b Hb; rewrite Hb; trivial.
          eapply match_stacks_inside_extcall with (F1 := j) (F2 := j') (m1 := m) (m1' := m2); eauto.
          intros; apply FwdSrc; eauto. intros; apply FwdTgt; eauto.
         (*intros; eapply external_call_max_perm; eauto. intros; eapply external_call_max_perm; eauto.*)
          red; intros. destruct (SEP _ _ _ J J'); split; trivial.
          (*split. destruct (Plt_Ple_dec b1 (Genv.genv_next ge)); trivial.
                   elim H5. unfold Mem.valid_block. xomega.*)
                 destruct (Plt_Ple_dec b2 (Genv.genv_next tge)); trivial.
                   elim H6. unfold Mem.valid_block. xomega.
          intros b Hb; apply FwdTgt; trivial.
          split; trivial.
            intros. destruct (SEP _ _ _ J J'). specialize (HL1 b1). specialize (HL2 b2).
            destruct (L1 b1). elim H5; eauto.
            destruct (L2 b2). elim H6; eauto. split; trivial. 
          intros b Hb; rewrite Hb; trivial.
          intros. exploit match_stacks_inside_globals_not_local; try eassumption.
                  intros [HH1 HH2]. rewrite HH1; simpl. apply freshblock_charF. left; trivial.
       -- eauto. -- auto. 
       -- destruct res; simpl; [apply agree_set_reg;auto|idtac|idtac]; eapply agree_regs_incr; eauto.
       -- auto. -- auto.
       -- eapply FwdTgt; eauto.
       -- eapply range_private_sub.
          ** eapply range_private_extcall; try eassumption.
             intros. eapply FwdSrc; eauto.
             intros. destruct (SEP _ _ _ H5 H6) as [_ VBsp]. intros ?; subst b'.
             elim VBsp. apply HL2; trivial.
          ** intros b Hb; rewrite Hb; trivial.
       -- eauto.
       -- intros. apply SSZ2. eapply external_call_max_perm; eauto.
       -- rewrite Lsp; trivial.
       -- rewrite Lsp'; trivial.
    ++ apply orb_true_iff in H5. destruct H5.
       eapply FwdSrc; eauto.
       unfold freshblock in H5. destruct (valid_block_dec m' b); trivial; discriminate.
    ++ apply orb_true_iff in H5. destruct H5.
       eapply FwdTgt; eauto.
       unfold freshblock in H5. destruct (valid_block_dec m2' b); trivial; discriminate.
    ++ remember (j b) as q; symmetry in Heqq; destruct q.
       -- destruct p. rewrite (INC _ _ _ Heqq) in H5; inv H5. 
          rewrite (HLL _ _ _ Heqq).
          assert (Fb: freshblock m m' b = false). { apply freshblock_charF. left. eapply Mem.valid_block_inject_1; eauto. }
          assert (Fb': freshblock m2 m2' b' = false). { apply freshblock_charF. left. eapply Mem.valid_block_inject_2; eauto. }
          rewrite Fb, Fb'; trivial.
       -- destruct (SEP _ _ _ Heqq H5).
          assert (Fb: freshblock m m' b = true). { apply freshblockProp_char. split; trivial. eapply Mem.valid_block_inject_1; eauto. }
          assert (Fb': freshblock m2 m2' b' = true). { apply freshblockProp_char. split; trivial. eapply Mem.valid_block_inject_2; eauto. }
          rewrite Fb, Fb'. do 2 rewrite orb_true_r; trivial.
    ++ eapply Ple_trans. apply GV1. apply forward_nextblock. assumption.
    ++ eapply Ple_trans. apply GV2. apply forward_nextblock. assumption.
    ++ admit. (*prove some lemma symbols_inject_incr_sep?*)
  * eexists. split. left. apply effstep_plus_one. 
    eapply effexec_Ibuiltin; eauto. 
    intros HH bb ofs EFF. right.
    eapply BuiltinEffects_propagate_injects; eassumption.

- (* cond *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  assert (eval_condition cond rs'##(sregs ctx args) m2 = Some b).
    eapply eval_condition_inject; eauto. eapply agree_val_regs; eauto.
  exists(State stk' f' (Vptr sp' Int.zero) (if b then spc ctx ifso else spc ctx ifnot) rs').
  exists m2, j, L1, L2.
  intuition.
  * split; trivial. intuition. 
    destruct b; econstructor; eauto.
  * eexists. split. left. apply effstep_plus_one. 
    eapply effexec_Icond; eauto.
    intros HH bb ofs EFF; inv EFF.

- (* jumptable *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  assert (Val.inject j rs#arg rs'#(sreg ctx arg)). eapply agree_val_reg; eauto.
  rewrite H0 in H2; inv H2.
  exists (State stk' f' (Vptr sp' Int.zero) (spc ctx pc') rs'), m2, j, L1, L2.
  intuition.
  * split; trivial. intuition. 
    econstructor; eauto.
  * eexists. split. left. apply effstep_plus_one. 
    eapply effexec_Ijumptable; eauto.
    rewrite list_nth_z_map. rewrite H1. simpl. reflexivity.
    intros HH bb ofs EFF; inv EFF.

- (* return *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
+ (* not inlined *)
  inv MS0; try congruence.
  assert (X: { m2' | Mem.free m2 sp' 0 (fn_stacksize f') = Some m2'}).
    apply Mem.range_perm_free. red; intros.
    destruct (zlt ofs f.(fn_stacksize)).
    replace ofs with (ofs + dstk ctx) by omega. eapply Mem.perm_inject; eauto.
    eapply Mem.free_range_perm; eauto. omega.
    inv FB. eapply range_private_perms; eauto.
    generalize (Zmax_spec (fn_stacksize f) 0). destruct (zlt 0 (fn_stacksize f)); omega.
  destruct X as [m2' FREE].
  specialize ( Mem.valid_block_free_1 _ _ _ _ _ H0); intros VB.
  specialize ( Mem.valid_block_free_1 _ _ _ _ _ FREE); intros VB'.
  exists (Returnstate stk' (regmap_optget (option_map (sreg ctx) or) Vundef rs')).
  exists m2', j, L1, L2.
  intuition.
  * eapply mini_locally_allocated_parallel_free; eassumption. 
  * split; trivial. intuition.
    econstructor; eauto.
       eapply match_stacks_bound with (bound := sp').
       eapply match_stacks_invariant; eauto.
         intros. eapply Mem.perm_free_3; eauto.
         intros. eapply Mem.perm_free_1; eauto.
         intros. eapply Mem.perm_free_3; eauto.
       erewrite Mem.nextblock_free; eauto. red in VBsp'; xomega.
       destruct or; simpl. apply agree_val_reg; auto. auto.
       eapply Mem.free_right_inject; eauto. eapply Mem.free_left_inject; eauto.
       (* show that no valid location points into the stack block being freed *)
       intros. inversion FB; subst.
       assert (PRIV': range_private L2 j m' m2 sp' (dstk ctx) f'.(fn_stacksize)).
       { rewrite H10 in PRIV. eapply range_private_free_left; eauto. }
       rewrite DSTK in PRIV'. destruct PRIV' as [L2sp' PRIV']. exploit (PRIV' (ofs + delta)). omega. intros [A B].
       eelim B; eauto. replace (ofs + delta - delta) with ofs by omega.
       apply Mem.perm_max with k. apply Mem.perm_implies with p; auto with mem.
    eapply Ple_trans; eauto. apply forward_nextblock. eapply free_forward; eauto.
    eapply Ple_trans; eauto. apply forward_nextblock. eapply free_forward; eauto.
  * eexists. split. left. apply effstep_plus_one. 
    eapply effexec_Ireturn; eauto.
    intros HH bb ofs EFF.
    apply FreeEffectD in EFF. destruct EFF as [SP' [VBsp'' BND]]; subst bb. left; trivial.

+ (* inlined *)
  exists (State stk' f' (Vptr sp' Int.zero) (spc ctx pc) rs'), m2, j, L1, L2.
  intuition.
  * red. erewrite freshblock_free; try eassumption. rewrite fresh_no_alloc.
    rewrite orb_false_r_ext. split; trivial.
  * split; trivial. intuition.
    ++ econstructor; eauto.
       eapply match_stacks_inside_invariant; eauto.
       intros. eapply Mem.perm_free_3; eauto.
       destruct or; simpl. apply agree_val_reg; auto. auto.
       eapply Mem.free_left_inject; eauto.
       inv FB. rewrite H7 in PRIV. eapply range_private_free_left; eauto.
    ++ eapply Mem.valid_block_free_1; eauto.
    ++ eapply Ple_trans; eauto. apply forward_nextblock. eapply free_forward; eauto.
  * eexists; split. right. split. simpl; omega. apply effstep_star_zero.
    intros HH bb ofs EFF; inv EFF.

- (* internal function, not inlined *)
  assert (A: exists f', tr_function cunit f f' /\ fd' = Internal f').
  { Errors.monadInv FD. exists x. split; auto. eapply transf_function_spec; eauto. }
  destruct A as [f' [TR1 EQ]].
  assert (TR: tr_function prog f f').
  { eapply tr_function_linkorder; eauto. }
  inversion TR; subst.
  exploit Mem.alloc_parallel_inject. eauto. eauto. apply Zle_refl.
    instantiate (1 := fn_stacksize f'). inv H1. xomega.
  intros [j' [m2' [sp' [A [B [C [D E]]]]]]].
  exists (State stk' f' (Vptr sp' Int.zero) (fn_entrypoint f') (init_regs args' (fn_params f'))).
  exists m2', j'.
  exists (fun b => L1 b || eq_block stk b). exists (fun b => L2 b || eq_block sp' b).
  intuition.
  * split; trivial; intros. specialize (E b1).
    destruct (eq_block stk b1); subst; simpl.
            ++ rewrite D in J'; inv J'.
              destruct (eq_block b2 b2); try congruence; simpl. split; apply orb_true_r.
            ++ rewrite E in J'; congruence. 
  * red; intros. specialize (E b1).
            destruct (eq_block b1 stk); subst; simpl.
            ++ rewrite J' in D; inv D.
               split. eapply Mem.fresh_block_alloc; eauto. 
               destruct (Plt_Ple_dec sp' (Genv.genv_next tge)); trivial.
                 elim (Mem.fresh_block_alloc _ _ _ _ _ A). unfold Mem.valid_block. xomega.
            ++ rewrite E in J'; trivial; congruence. 
  * red. erewrite freshblock_alloc; try eassumption.
            erewrite freshblock_alloc; try eassumption. split; trivial. 
  * split; trivial. intuition.
    + rewrite H6. 
      assert (HL2': L2 sp' || eq_block sp' sp' = true).
      { destruct (eq_block sp' sp'); try congruence. apply orb_true_r. } 
      econstructor.
      (*instantiate (1 := j').*) apply match_stacks_inside_base.
      assert (SP: sp' = Mem.nextblock m2) by (eapply Mem.alloc_result; eauto).
      rewrite <- SP in MS0.
      eapply match_stacks_sub.
      -- eapply match_stacks_invariant with (m':=m2); eauto.
          intros. eapply Mem.valid_block_alloc; eauto.
          intros. destruct (eq_block b1 stk).
          subst b1. rewrite D in H7; inv H7. subst b2. eelim Plt_strict; eauto.
          rewrite E in H7; auto.
          intros. exploit Mem.perm_alloc_inv. eexact H. eauto.
          destruct (eq_block b1 stk); intros; auto.
          subst b1. rewrite D in H7; inv H7. subst b2. eelim Plt_strict; eauto.
          intros. eapply Mem.perm_alloc_1; eauto.
          intros. exploit Mem.perm_alloc_inv. eexact A. eauto.
          rewrite dec_eq_false; auto.
      -- solve [intros b Hb; rewrite Hb; trivial].
      -- solve [intros b Hb; rewrite Hb; trivial]. 
      -- intros. exploit match_stacks_globals_not_local; try eassumption.
         intros [HH1 HH2]; rewrite HH1; simpl. destruct (eq_block sp' b'); trivial.
         subst b' sp'. eelim Mem.fresh_block_alloc; try apply A; trivial.  
      -- auto.
      -- auto.
      -- apply HL2'.
      -- eassumption.
      -- auto.
      -- rewrite H5. apply agree_regs_init_regs. eauto. auto. inv H1; auto.
      -- congruence.
      -- auto.
      -- eapply Mem.valid_new_block; eauto.
      -- split; trivial; intros. split.
          eapply Mem.perm_alloc_2; eauto. inv H1; xomega.
          intros; red; intros. exploit Mem.perm_alloc_inv. eexact H. eauto.
          destruct (eq_block b stk); intros.
          subst. rewrite D in H10; inv H10. inv H1; xomega.
          rewrite E in H10; auto. eelim Mem.fresh_block_alloc. eexact A. eapply Mem.mi_mappedblocks; eauto.
      -- auto.
      -- intros. exploit Mem.perm_alloc_inv; eauto. rewrite dec_eq_true. omega.
      -- destruct (eq_block stk stk); try congruence. apply orb_true_r.
      -- assumption. 
    + apply orb_true_iff in H7; destruct H7.
      -- eapply Mem.valid_block_alloc; eauto.
      -- destruct (eq_block stk b); try discriminate. subst b. eapply Mem.valid_new_block; eauto. 
    + apply orb_true_iff in H7; destruct H7.
      -- eapply Mem.valid_block_alloc; eauto.
      -- destruct (eq_block sp' b); try discriminate. subst b. eapply Mem.valid_new_block; eauto. 
    + specialize (E b).
      destruct (eq_block stk b); subst; simpl.
     -- rewrite D in H7; inv H7. destruct (eq_block b' b'); try congruence; simpl. do 2 rewrite orb_true_r; trivial.
     -- rewrite E in H7; try congruence.
       destruct (eq_block sp' b'); subst; simpl.
       ** elim (Mem.fresh_block_alloc _ _ _ _ _ A). eapply MINJ; eauto.
       ** do 2 rewrite orb_false_r; eauto. 
    + eapply Ple_trans; eauto. apply forward_nextblock. eapply alloc_forward; eauto.
    + eapply Ple_trans; eauto. apply forward_nextblock. eapply alloc_forward; eauto.
    + admit. (*prove some lemma symbols_inject_incr_sep?*) 
  * eexists; split. left. apply effstep_plus_one.
     eapply effexec_function_internal; eauto.
    intros HH bb ofs EFF; inv EFF.

- (* internal function, inlined *)
  inversion FB; subst. 
  exploit Mem.alloc_left_mapped_inject.
    eauto.
    eauto.
    (* sp' is valid *)
    instantiate (1 := sp'). auto.
    (* offset is representable *)
    instantiate (1 := dstk ctx). generalize (Zmax2 (fn_stacksize f) 0). omega.
    (* size of target block is representable *)
    intros. right. exploit SSZ2; eauto with mem. inv FB; omega.
    (* we have full permissions on sp' at and above dstk ctx *)
    intros. apply Mem.perm_cur. apply Mem.perm_implies with Freeable; auto with mem.
    eapply range_private_perms; eauto. xomega.
    (* offset is aligned *)
    replace (fn_stacksize f - 0) with (fn_stacksize f) by omega.
    inv FB. apply min_alignment_sound; auto.
    (* nobody maps to (sp, dstk ctx...) *)
    intros. destruct PRIV as [L2sp' PRIV]. exploit (PRIV (ofs + delta')); eauto. xomega.
    intros [A B]. eelim B; eauto.
    replace (ofs + delta' - delta') with ofs by omega.
    apply Mem.perm_max with k. apply Mem.perm_implies with p; auto with mem.
  intros [F' [A [B [C D]]]].
  exploit tr_moves_init_regs; eauto. intros [rs'' [P [Q R]]].

  eexists (State stk' f' (Vptr sp' Int.zero) (spc ctx (fn_entrypoint f)) rs''), m2, F'.
  exists (fun b => L1 b || eq_block stk b), L2.
  intuition.
  * clear P.
    split; trivial; intros. specialize (D b1).
    destruct (eq_block stk b1); subst; simpl.
    ++ rewrite C in J'; inv J'. rewrite orb_true_r; split; trivial.
    ++ rewrite D in J'; congruence.
  * clear P.
    red; intros. specialize (D b1).
    destruct (eq_block b1 stk); subst; simpl.
    ++ rewrite C in J'; inv J'.
       split. eapply (Mem.fresh_block_alloc _ _ _ _ _ H). 
       destruct (Plt_Ple_dec b2 (Genv.genv_next tge)); trivial.
       exploit match_stacks_inside_globals_not_local; try eassumption. intros [AA BB]. congruence.
    ++ rewrite D in J'; congruence.
  * clear P. red. erewrite freshblock_alloc; try eassumption.
            erewrite fresh_no_alloc. split; trivial. 
  * clear P. split; trivial. intuition.
    ++ econstructor. 
       { eapply match_stacks_inside_sub.
         + eapply match_stacks_inside_alloc_left; eauto.
           eapply match_stacks_inside_invariant; eauto.
           omega. 
         + intros b Hb; rewrite Hb; trivial.  
         + trivial.
         + eapply match_stacks_inside_globals_not_local; try eassumption. }
       eauto. auto.
       apply agree_regs_incr with j; auto.
       auto. auto. auto.
       rewrite H2. eapply range_private_alloc_left; eauto.
       auto. auto.
       { destruct (eq_block stk stk); try congruence. apply orb_true_r. }
       { apply PRIV. }
    ++ apply orb_true_iff in H8; destruct H8.
      -- eapply Mem.valid_block_alloc; eauto.
      -- destruct (eq_block stk b); try discriminate. subst b. eapply Mem.valid_new_block; eauto.
    ++ specialize (D b).
       destruct (eq_block stk b); subst; simpl.
       -- rewrite C in H8; inv H8. destruct PRIV as [L2b' PRIV]. rewrite L2b'; apply orb_true_r.
       -- rewrite D in H8; try congruence. rewrite orb_false_r. eauto.
    ++ eapply Ple_trans; eauto. eapply forward_nextblock. eapply alloc_forward; eauto. 
    ++ admit. (*prove some lemma symbols_inject_incr_sep?*) 
 * eexists; split. left. eapply effstep_plus_star_trans'. apply effstep_plus_one.
     eapply effexec_Inop; eauto.
     eexact P. reflexivity.
    intros HH bb ofs EFF; inv EFF.
     
- (* external function - COMPCOMP: now restricted to helpers*)
  exploit match_stacks_globalenvs; eauto. intros [bound MG].
  exploit (nonobservables_mem_inject ge tge); try eassumption.
  { apply EFhelpers; trivial. }
  { eapply match_globalenvs_preserves_globals; eauto. }
  intros [j' [v1 [m2' [A [B [C [D [E [INC SEP]]]]]]]]].
  simpl in FD. inv FD. 
  assert (FwdSrc: mem_forward m m') by (eapply external_call_mem_forward; eauto).
  assert (FwdTgt: mem_forward m2 m2') by (eapply external_call_mem_forward; eauto).
  exists (Returnstate stk' v1), m2', j'.
  exists (fun b => L1 b || freshblock m m' b), (fun b => L2 b || freshblock m2 m2' b).
  assert (GSEP: globals_separate m tge j j').
  { red; intros. destruct (SEP _ _ _ J J').
    split; trivial.
    destruct (Plt_Ple_dec b2 (Genv.genv_next tge)); trivial.
             elim H1. unfold Mem.valid_block; xomega. } 
  intuition.
  * split; trivial; intros.
    destruct (SEP _ _ _ J J') as [vb vb'].
    assert (Fb: freshblock m m' b1 = true). { apply freshblockProp_char. split; trivial. eapply Mem.valid_block_inject_1; eauto. }
    assert (Fb': freshblock m2 m2' b2 = true). { apply freshblockProp_char. split; trivial. eapply Mem.valid_block_inject_2; eauto. }
    rewrite Fb, Fb'. split; apply orb_true_r.
  * split; trivial.
  * split. reflexivity. intuition.
    ++ econstructor.
       eapply match_stacks_bound with (Mem.nextblock m2); trivial.
       -- eapply match_stacks_sub with (L:=L1). 2: intros b Hb; rewrite Hb; trivial.
          eapply match_stacks_extcall with (F1 := j) (F2 := j') (m1 := m) (m1' := m2); eauto.
          intros; apply FwdSrc; eauto. intros; apply FwdTgt; eauto.
          intros b Hb; apply FwdTgt; trivial.
          xomega.
          split; trivial.
            intros. destruct (SEP _ _ _ J J'). specialize (HL1 b1). specialize (HL2 b2).
            destruct (L1 b1). elim H0; eauto.
            destruct (L2 b2). elim H1; eauto. split; trivial. 
          intros b Hb; rewrite Hb; trivial.
          intros. exploit match_stacks_globals_not_local; try eassumption.
                  intros [HH1 HH2]. rewrite HH1; simpl. apply freshblock_charF. left; trivial.
       -- eapply mem_forward_nextblock; trivial.
       -- trivial.
       -- trivial.
    ++ apply orb_true_iff in H0. destruct H0.
       eapply FwdSrc; eauto.
       unfold freshblock in H0. destruct (valid_block_dec m' b); trivial; discriminate.
    ++ apply orb_true_iff in H0. destruct H0.
       eapply FwdTgt; eauto.
       unfold freshblock in H0. destruct (valid_block_dec m2' b); trivial; discriminate.
    ++ remember (j b) as q; symmetry in Heqq; destruct q.
       -- destruct p. rewrite (INC _ _ _ Heqq) in H0; inv H0. 
          rewrite (HLL _ _ _ Heqq).
          assert (Fb: freshblock m m' b = false). { apply freshblock_charF. left. eapply Mem.valid_block_inject_1; eauto. }
          assert (Fb': freshblock m2 m2' b' = false). { apply freshblock_charF. left. eapply Mem.valid_block_inject_2; eauto. }
          rewrite Fb, Fb'; trivial.
       -- destruct (SEP _ _ _ Heqq H0).
          assert (Fb: freshblock m m' b = true). { apply freshblockProp_char. split; trivial. eapply Mem.valid_block_inject_1; eauto. }
          assert (Fb': freshblock m2 m2' b' = true). { apply freshblockProp_char. split; trivial. eapply Mem.valid_block_inject_2; eauto. }
          rewrite Fb, Fb'. do 2 rewrite orb_true_r; trivial.
    ++ eapply Ple_trans; eauto. apply forward_nextblock; eauto.
    ++ eapply Ple_trans; eauto. apply forward_nextblock; eauto.
    ++ admit. (*prove some lemma symbols_inject_incr_sep?*) 
  * eexists; split. left. eapply effstep_plus_one. 
    eapply effexec_function_external; eauto.
    intros HH bb ofs EFF. right.
    eapply BuiltinEffects_propagate_injects; eassumption. 

- (* return fron noninlined function *)
  inv MS0.
+ (* normal case *)
  exists (State stk'0 f' (Vptr sp' Int.zero) (spc ctx pc) rs' # (sreg ctx res) <- v').
  exists m2, j, L1, L2.
  intuition.
  * split; trivial. intuition.
    econstructor; eauto.
    apply match_stacks_inside_set_reg; auto.
    apply agree_set_reg; auto.
  * eexists; split. left. apply effstep_plus_one.
     eapply effexec_return.
    intros HH bb ofs EFF; inv EFF.
+ (* untailcall case *)
  inv MS; try congruence.
  rewrite RET in RET0; inv RET0.
  exists (State stk'0 f' (Vptr sp' Int.zero) (spc ctx' pc) rs' # (sreg ctx' res) <- v').
  exists m2, j, L1, L2. intuition.
  * split; trivial. intuition.
    eapply match_regular_states.
    eapply match_stacks_inside_set_reg; eauto.
    eauto. auto.
    apply agree_set_reg; auto.
    auto. auto. auto.
    destruct PRIV as [L2sp' PRIV]. split; trivial; intros. destruct (zlt ofs (dstk ctx)). apply PAD; omega. apply PRIV; omega.
    auto. auto. trivial. trivial.
  * eexists; split. left. apply effstep_plus_one.
     eapply effexec_return.
    intros HH bb ofs EFF; inv EFF.

- (* return from inlined function *)
  inv MS0; try congruence. rewrite RET0 in RET; inv RET.
  unfold inline_return in AT.
  assert (PRIV': range_private L2 j m m2 sp' (dstk ctx' + mstk ctx') f'.(fn_stacksize)).
  { destruct PRIV as [L2sp' PRIV]. split; trivial; intros.
    destruct (zlt ofs (dstk ctx)). apply PAD. omega. apply PRIV. omega. }
  destruct or.
  * (* with a result *)
    exists (State stk' f' (Vptr sp' Int.zero) (spc ctx' pc) rs' # (sreg ctx' res) <- (rs' # (sreg ctx r))).
    exists m2, j, L1, L2.
    intuition.
    ++ split; trivial. intuition.
       econstructor; eauto. apply match_stacks_inside_set_reg; auto. apply agree_set_reg; auto.
    ++ eexists; split. left. apply effstep_plus_one.
      eapply effexec_Iop; eauto. (*simpl. reflexivity.*)
      intros HH bb ofs EFF; inv EFF.
  * (* without a result *)
    exists (State stk' f' (Vptr sp' Int.zero) (spc ctx' pc) rs').
    exists m2, j, L1, L2.
    intuition.
    ++ split; trivial. intuition.
       econstructor; eauto. subst vres. apply agree_set_reg_undef'; auto. 
    ++ eexists; split. left. apply effstep_plus_one.
      eapply effexec_Inop; eauto. 
      intros HH bb ofs EFF; inv EFF.
Admitted.

Lemma matchstates_inject L L' j st m st' m' (MS:match_states L L' j st m st' m'): Mem.inject j m m'.
Proof. inv MS; trivial. Qed.

Require Import minisepcomp.val_casted.

Definition SIM: Mini_simulation_inj.Mini_simulation_inject RTL_eff_sem RTL_eff_sem ge tge.
eapply inj_simulation_plus_typed.
+ apply senv_preserved. 
+ instantiate (1:= fun d j L1 c1 m1 L2 c2 m2  => match_cores d j L1 c1 m1 L2 c2 m2 /\
      mem_respects_readonly ge m1 /\ mem_respects_readonly tge m2);  intros.
  red. destruct MS as [[? [MC [HH1 [HH2 HH3]]]] [MRSrc MRtgt]]; subst.
  split; trivial. split; trivial.
  intros. apply matchstates_inject in MC. split. eapply Mem.valid_block_inject_1; eauto. eapply Mem.valid_block_inject_2; eauto. 
+ intros. destruct MS as [[? [MS [HL1 [HL2 [HLL [GV1 [GV2 SINV]]]]]]] [MRSrc MRtgt]]; subst; eauto.
+ admit. (*globalenvs property*)
+ (*init*)
  intros.
  assert (Ple (Genv.genv_next ge) (Mem.nextblock m1) /\ Ple (Genv.genv_next tge) (Mem.nextblock m2)).
  { admit. (*add to init-clause?*) }
  destruct H6 as [GV1 GV2].
  destruct v; inv H. simpl. destruct (Int.eq_dec i Int.zero); inv H7.
  remember (Genv.find_funct_ptr ge b) as q; symmetry in Heqq; destruct q; inv H6.
  exploit function_ptr_translated; eauto. intros (cu & tf & FIND & TR & LINK). 
  rewrite FIND. 
  destruct f; inv H7. apply Errors.bind_inversion in TR.
  destruct TR as [f' [Tf OKINT]]. inv OKINT. 
  rewrite <- (mem_lemmas.Forall2_Zlength H1).
  remember (val_has_type_list_func vals1 (sig_args (fn_sig f)) &&
       vals_defined vals1) as d.
  symmetry in Heqd; destruct d; try discriminate. simpl in *.
  apply andb_true_iff in Heqd; destruct Heqd.
  assert (fn_sig f' = fn_sig f).
  { unfold transf_function in Tf. remember (expand_function (funenv_program cu) f initstate) as z; destruct z; try discriminate.
    destruct (zlt (st_stksize s') Int.max_unsigned); try discriminate. inv Tf. simpl in *; trivial. }
  rewrite H8 in *.
  erewrite vals_inject_defined; eauto. 2: eapply forall_inject_val_list_inject; eauto.
  erewrite val_list_inject_hastype; eauto. 2: eapply forall_inject_val_list_inject; eauto.
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
      end Int.max_unsigned); inv H6; simpl.
  eexists.
  split. reflexivity. 
  split. 
  - split. reflexivity.
    split; trivial; try discriminate.
    * econstructor; eauto.
      2: solve [simpl; unfold Errors.bind; rewrite Tf; trivial].
      2: solve [apply forall_inject_val_list_inject; trivial].
      clear l H1.  destruct H2 as [Q1 [Q2 Q3]]. destruct H3 as [K1 [K2 [K3 K4]]].
      admit. (*globals envs*)
    * intuition.
  - split; trivial.
+ (*halted*)
  intros. destruct H as [[? [MS [? [? [? [? ?]]]]]] [MRSrc MRTgt]]; subst.
  destruct c1; inv H0.
  destruct stack; inv H6. inv MS.
  - apply match_stacks_empty in MS0; trivial. subst. 
    exists v'. intuition. 
  - simpl. apply match_stacks_inside_empty in MS0; trivial. destruct MS0; subst. congruence.
+ (*at_external*)
  intros. destruct H as [[? [MS [? [? [? [? ?]]]]]][MRSrc MRTgt]]; subst.
  destruct c1; inv H0. destruct f; inv H6.
  remember (observableEF_dec e0) as obs; destruct obs; inv H0.
  simpl in *. inv MS. intuition.
  exists args'.
  split. apply mem_lemmas.val_list_inject_forall_inject; trivial.
  simpl. inv FD. rewrite <- Heqobs; trivial.
+ (*after_external*)
  intros. destruct MatchMu as [[? [MS [? [? [? [GV1 [GV2 SINJ]]]]]]][MRSrc MRTgt]]; subst.
  destruct st1; inv AtExtSrc. destruct f; inv H3.
  remember (observableEF_dec e0) as obs; destruct obs; inv H4.
  simpl in *. inv MS. simpl. inv FD.
  eexists; eexists. split. reflexivity. split. reflexivity.
  split.
  - split; trivial.
    split. 
    * econstructor; trivial.
           eapply match_stacks_bound. instantiate (1:=Mem.nextblock m2).
           2: eapply forward_nextblock; eassumption.
           eapply match_stacks_extcall.
           Focus 7. eapply match_stacks_bound. eassumption. xomega. 
           intros. eapply FwdSrc; trivial.
           intros. eapply FwdTgt; trivial.
           eapply mem_unchanged_on_sub_strong. eassumption. trivial.
           (*   unfold loc_out_of_reach, o_o_reach. intros. trivial. split; trivial.*)
           trivial.
           trivial.
           apply FwdTgt.
           xomega.
           trivial.
    * intuition.
           { eapply FwdSrc; eauto. } 
           { eapply FwdTgt; eauto. }
           { destruct INC as [INC SEP].
             remember (j b) as q; symmetry in Heqq; destruct q.
             * destruct p. specialize (H2 _ _ _ Heqq).
               rewrite (INC _ _ _ Heqq) in H; inv H; trivial.
             * destruct (SEP _ _ _ Heqq H) as [A B]; rewrite B; trivial. }
           { eapply Ple_trans; eauto. eapply forward_nextblock; trivial. }
           { eapply Ple_trans; eauto. eapply forward_nextblock; trivial. }
           admit. (*symbols_inject_incr*)
  - split; eapply mem_respects_readonly_forward'; eassumption. 
+ (*corediagram*)
  intros. destruct H0 as [MS [MRSrc MRTgt]]; subst.
  exploit core_diagram; eauto.
  intros [st2' [m2' [j' [L1' [L2' [INC [SEP [LOC [MATCH [U2 [TSTEPS HU]]]]]]]]]]]. 
  exists st2', m2', j', L1', L2'. split; trivial. split; trivial. split; trivial.
  split.
  - split; trivial.
    split. exploit semantics_lemmas.mem_step_readonly. eapply effstep_mem. apply H.
           intros [Fwd RD]. eapply mem_respects_readonly_fwd; eauto.
    exploit semantics_lemmas.mem_step_readonly.
      destruct TSTEPS. eapply effstep_plus_mem; eauto.  eapply effstep_star_mem; eapply a. 
    intros [Fwd RD]. eapply mem_respects_readonly_fwd; eauto.
  - exists U2. split; eassumption. 
Admitted.

End INLINING.