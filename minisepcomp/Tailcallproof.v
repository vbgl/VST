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

(** Recognition of tail calls: correctness proof *)

Require Import Coqlib Maps Integers AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import minisepcomp.Op minisepcomp.Registers minisepcomp.RTL_memsem minisepcomp.Conventions minisepcomp.Tailcall.
Require Import minisepcomp.BuiltinEffects.

(** * Syntactic properties of the code transformation *)

(** ** Measuring the number of instructions eliminated *)

(** The [return_measure c pc] function counts the number of instructions
  eliminated by the code transformation, where [pc] is the successor
  of a call turned into a tailcall.  This is the length of the
  move/nop/return sequence recognized by the [is_return] boolean function.
*)

Fixpoint return_measure_rec (n: nat) (c: code) (pc: node)
                            {struct n}: nat :=
  match n with
  | O => O
  | S n' =>
      match c!pc with
      | Some(Inop s) => S(return_measure_rec n' c s)
      | Some(Iop op args dst s) => S(return_measure_rec n' c s)
      | _ => O
      end
  end.

Definition return_measure (c: code) (pc: node) :=
  return_measure_rec niter c pc.

Lemma return_measure_bounds:
  forall f pc, (return_measure f pc <= niter)%nat.
Proof.
  intro f.
  assert (forall n pc, (return_measure_rec n f pc <= n)%nat).
    induction n; intros; simpl.
    omega.
    destruct (f!pc); try omega.
    destruct i; try omega.
    generalize (IHn n0). omega.
    generalize (IHn n0). omega.
  intros. unfold return_measure. apply H.
Qed.

Remark return_measure_rec_incr:
  forall f n1 n2 pc,
  (n1 <= n2)%nat ->
  (return_measure_rec n1 f pc <= return_measure_rec n2 f pc)%nat.
Proof.
  induction n1; intros; simpl.
  omega.
  destruct n2. omegaContradiction. assert (n1 <= n2)%nat by omega.
  simpl. destruct f!pc; try omega. destruct i; try omega.
  generalize (IHn1 n2 n H0). omega.
  generalize (IHn1 n2 n H0). omega.
Qed.

Lemma is_return_measure_rec:
  forall f n n' pc r,
  is_return n f pc r = true -> (n <= n')%nat ->
  return_measure_rec n f.(fn_code) pc = return_measure_rec n' f.(fn_code) pc.
Proof.
  induction n; simpl; intros.
  congruence.
  destruct n'. omegaContradiction. simpl.
  destruct (fn_code f)!pc; try congruence.
  destruct i; try congruence.
  decEq. apply IHn with r. auto. omega.
  destruct (is_move_operation o l); try congruence.
  destruct (Reg.eq r r1); try congruence.
  decEq. apply IHn with r0. auto. omega.
Qed.

(** ** Relational characterization of the code transformation *)

(** The [is_return_spec] characterizes the instruction sequences
  recognized by the [is_return] boolean function.  *)

Inductive is_return_spec (f:function): node -> reg -> Prop :=
  | is_return_none: forall pc r,
      f.(fn_code)!pc = Some(Ireturn None) ->
      is_return_spec f pc r
  | is_return_some: forall pc r,
      f.(fn_code)!pc = Some(Ireturn (Some r)) ->
      is_return_spec f pc r
  | is_return_nop: forall pc r s,
      f.(fn_code)!pc = Some(Inop s) ->
      is_return_spec f s r ->
      (return_measure f.(fn_code) s < return_measure f.(fn_code) pc)%nat ->
      is_return_spec f pc r
  | is_return_move: forall pc r r' s,
      f.(fn_code)!pc = Some(Iop Omove (r::nil) r' s) ->
      is_return_spec f s r' ->
      (return_measure f.(fn_code) s < return_measure f.(fn_code) pc)%nat ->
     is_return_spec f pc r.

Lemma is_return_charact:
  forall f n pc rret,
  is_return n f pc rret = true -> (n <= niter)%nat ->
  is_return_spec f pc rret.
Proof.
  induction n; intros.
  simpl in H. congruence.
  generalize H. simpl.
  caseEq ((fn_code f)!pc); try congruence.
  intro i. caseEq i; try congruence.
  intros s; intros. eapply is_return_nop; eauto. eapply IHn; eauto. omega.
  unfold return_measure.
  rewrite <- (is_return_measure_rec f (S n) niter pc rret); auto.
  rewrite <- (is_return_measure_rec f n niter s rret); auto.
  simpl. rewrite H2. omega. omega.

  intros op args dst s EQ1 EQ2.
  caseEq (is_move_operation op args); try congruence.
  intros src IMO. destruct (Reg.eq rret src); try congruence.
  subst rret. intro.
  exploit is_move_operation_correct; eauto. intros [A B]. subst.
  eapply is_return_move; eauto. eapply IHn; eauto. omega.
  unfold return_measure.
  rewrite <- (is_return_measure_rec f (S n) niter pc src); auto.
  rewrite <- (is_return_measure_rec f n niter s dst); auto.
  simpl. rewrite EQ2. omega. omega.

  intros or EQ1 EQ2. destruct or; intros.
  assert (r = rret). eapply proj_sumbool_true; eauto. subst r.
  apply is_return_some; auto.
  apply is_return_none; auto.
Qed.

(** The [transf_instr_spec] predicate relates one instruction in the
  initial code with its possible transformations in the optimized code. *)

Inductive transf_instr_spec (f: function): instruction -> instruction -> Prop :=
  | transf_instr_tailcall: forall sig ros args res s,
      f.(fn_stacksize) = 0 ->
      is_return_spec f s res ->
      transf_instr_spec f (Icall sig ros args res s) (Itailcall sig ros args)
  | transf_instr_default: forall i,
      transf_instr_spec f i i.

Lemma transf_instr_charact:
  forall f pc instr,
  f.(fn_stacksize) = 0 ->
  transf_instr_spec f instr (transf_instr f pc instr).
Proof.
  intros. unfold transf_instr. destruct instr; try constructor.
  caseEq (is_return niter f n r && tailcall_is_possible s &&
          opt_typ_eq (sig_res s) (sig_res (fn_sig f))); intros.
  destruct (andb_prop _ _ H0). destruct (andb_prop _ _ H1).
  eapply transf_instr_tailcall; eauto.
  eapply is_return_charact; eauto.
  constructor.
Qed.

Lemma transf_instr_lookup:
  forall f pc i,
  f.(fn_code)!pc = Some i ->
  exists i',  (transf_function f).(fn_code)!pc = Some i' /\ transf_instr_spec f i i'.
Proof.
  intros. unfold transf_function.
  destruct (zeq (fn_stacksize f) 0).
  simpl. rewrite PTree.gmap. rewrite H. simpl.
  exists (transf_instr f pc i); split. auto. apply transf_instr_charact; auto.
  exists i; split. auto. constructor.
Qed.

(** * Semantic properties of the code transformation *)

(** ** The ``less defined than'' relation between register states *)

(** A call followed by a return without an argument can be turned
  into a tail call.  In this case, the original function returns
  [Vundef], while the transformed function can return any value.
  We account for this situation by using the ``less defined than''
  relation between values and between memory states.  We need to
  extend it pointwise to register states. *)

Lemma regs_lessdef_init_regs:
  forall params vl vl',
  Val.lessdef_list vl vl' ->
  regs_lessdef (init_regs vl params) (init_regs vl' params).
Proof.
  induction params; intros.
  simpl. red; intros. rewrite Regmap.gi. constructor.
  simpl. inv H.   red; intros. rewrite Regmap.gi. constructor.
  apply set_reg_lessdef. auto. auto.
Qed.

(** * Proof of semantic preservation *)

Definition match_prog (p tp: RTL_memsem.program) :=
  match_program (fun cu f tf => tf = transf_fundef f) eq p tp.

Lemma transf_program_match:
  forall p, match_prog p (transf_program p).
Proof.
  intros. apply match_transform_program; auto.
Qed.

Section PRESERVATION.

Variable prog tprog: program.
Hypothesis TRANSL: match_prog prog tprog.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_transf TRANSL).

Lemma functions_translated:
  forall (v: val) (f: RTL_memsem.fundef),
  Genv.find_funct ge v = Some f ->
  Genv.find_funct tge v = Some (transf_fundef f).
Proof (Genv.find_funct_transf TRANSL).

Lemma funct_ptr_translated:
  forall (b: block) (f: RTL_memsem.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  Genv.find_funct_ptr tge b = Some (transf_fundef f).
Proof (Genv.find_funct_ptr_transf TRANSL).

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof (Genv.senv_transf TRANSL).

Lemma sig_preserved:
  forall f, funsig (transf_fundef f) = funsig f.
Proof.
  destruct f; auto. simpl. unfold transf_function.
  destruct (zeq (fn_stacksize f) 0); auto.
Qed.

Lemma stacksize_preserved:
  forall f, fn_stacksize (transf_function f) = fn_stacksize f.
Proof.
  unfold transf_function. intros.
  destruct (zeq (fn_stacksize f) 0); auto.
Qed.

Lemma find_function_translated:
  forall ros rs rs' f,
  find_function ge ros rs = Some f ->
  regs_lessdef rs rs' ->
  find_function tge ros rs' = Some (transf_fundef f).
Proof.
  intros until f; destruct ros; simpl.
  intros.
  assert (rs'#r = rs#r).
    exploit Genv.find_funct_inv; eauto. intros [b EQ].
    generalize (H0 r). rewrite EQ. intro LD. inv LD. auto.
  rewrite H1. apply functions_translated; auto.
  rewrite symbols_preserved. destruct (Genv.find_symbol ge i); intros.
  apply funct_ptr_translated; auto.
  discriminate.
Qed.

(** Consider an execution of a call/move/nop/return sequence in the
  original code and the corresponding tailcall in the transformed code.
  The transition sequences are of the following form
  (left: original code, right: transformed code).
  [f] is the calling function and [fd] the called function.
<<
     State stk f (Icall instruction)       State stk' f' (Itailcall)

     Callstate (frame::stk) fd args        Callstate stk' fd' args'
            .                                       .
            .                                       .
            .                                       .
     Returnstate (frame::stk) res          Returnstate stk' res'

     State stk f (move/nop/return seq)
            .
            .
            .
     State stk f (return instr)

     Returnstate stk res
>>
The simulation invariant must therefore account for two kinds of
mismatches between the transition sequences:
- The call stack of the original program can contain more frames
  than that of the transformed program (e.g. [frame] in the example above).
- The regular states corresponding to executing the move/nop/return
  sequence must all correspond to the single [Returnstate stk' res']
  state of the transformed program.

We first define the simulation invariant between call stacks.
The first two cases are standard, but the third case corresponds
to a frame that was eliminated by the transformation. *)

(*COMPCOMP adaptation: original type of the reltion was:
  Inductive match_stackframes: list stackframe -> list stackframe -> Prop.
  We add the component (L:block-> bool) and require that the stack blocks sp of
  the src execution are local*)

Inductive match_stackframes: list stackframe -> (block -> bool) -> list stackframe -> Prop :=
  | match_stackframes_nil L:
      match_stackframes nil L nil
  | match_stackframes_normal: forall stk stk' res sp pc rs rs' f L,
      match_stackframes stk L stk' ->
      regs_lessdef rs rs' ->
      L sp = true ->
      match_stackframes
        (Stackframe res f (Vptr sp Int.zero) pc rs :: stk) L
        (Stackframe res (transf_function f) (Vptr sp Int.zero) pc rs' :: stk')
  | match_stackframes_tail: forall stk stk' res sp pc rs f L,
      match_stackframes stk L stk' ->
      is_return_spec f pc res ->
      f.(fn_stacksize) = 0 ->
      L sp = true ->
      match_stackframes
        (Stackframe res f (Vptr sp Int.zero) pc rs :: stk) L
        stk'.

(*COMCOMP adaptation: removed memory components from all 3 state constructors*)
Definition measure (st: state) : nat :=
  match st with
  | State s f sp pc rs (*m*) => (List.length s * (niter + 2) + return_measure f.(fn_code) pc + 1)%nat
  | Callstate s f args (*m*) => 0%nat
  | Returnstate s v (*m*) => (List.length s * (niter + 2))%nat
  end.

Ltac TransfInstr :=
  match goal with
  | H: (PTree.get _ (fn_code _) = _) |- _ =>
      destruct (transf_instr_lookup _ _ _ H) as [i' [TINSTR TSPEC]]; inv TSPEC
  end.

Ltac EliminatedInstr :=
  match goal with
  | H: (is_return_spec _ _ _) |- _ => inv H; try congruence
  | _ => idtac
  end.

(** Here is the invariant relating two states.  The first three
  cases are standard.  Note the ``less defined than'' conditions
  over values and register states, and the corresponding ``extends''
  relation over memory states. *)

(*COMPCOMP adaptation: in the first 3 rules, just promote the local_blocks info 
  from match_stackframes. Again we ensure that sp is local*)
Inductive match_state : RTL_memsem.state -> mem -> (block -> bool) -> RTL_memsem.state -> mem -> Prop := 
  | match_states_normal:
      forall s sp pc rs m s' rs' m' f L
             (STACKS: match_stackframes s L s')
             (RLD: regs_lessdef rs rs')
             (MLD: Mem.extends m m')
             (Lsp: L sp = true),
      match_state (State s f (Vptr sp Int.zero) pc rs) m L
                   (State s' (transf_function f) (Vptr sp Int.zero) pc rs') m'
  | match_states_call:
      forall s f args m s' args' m' L,
      match_stackframes s L s' ->
      Val.lessdef_list args args' ->
      Mem.extends m m' ->
      match_state (Callstate s f args) m L
                   (Callstate s' (transf_fundef f) args') m'
  | match_states_return:
      forall s v m s' v' m' L,
      match_stackframes s L s' ->
      Val.lessdef v v' ->
      Mem.extends m m' ->
      match_state (Returnstate s v) m L
                   (Returnstate s' v') m'
  | match_states_interm:
      forall s sp pc rs m s' m' f r v' L
             (STACKS: match_stackframes s L s')
             (MLD: Mem.extends m m')
             (Lsp: L sp = true),
      is_return_spec f pc r ->
      f.(fn_stacksize) = 0 ->
      Val.lessdef (rs#r) v' ->
      match_state (State s f (Vptr sp Int.zero) pc rs) m L
                  (Returnstate s' v') m'.

(** The last case of [match_states] corresponds to the execution
  of a move/nop/return sequence in the original code that was
  eliminated by the transformation:
<<
     State stk f (move/nop/return seq)  ~~  Returnstate stk' res'
            .
            .
            .
     State stk f (return instr)         ~~  Returnstate stk' res'
>>
  To preserve non-terminating behaviors, we need to make sure
  that the execution of this sequence in the original code cannot
  diverge.  For this, we introduce the following complicated
  measure over states, which will decrease strictly whenever
  the original code makes a transition but the transformed code
  does not. *)

Require Import minisepcomp.mini_simulations.
Require Import minisepcomp.mini_simulations_lemmas.
Require Import msl.Axioms. (*for extensionality*)
Require Import sepcomp.mem_lemmas. 

Definition core_data:Type := RTL_memsem.state.
Definition match_states (cd:core_data) (st:state) (m:mem) (L:block -> bool) (st':state) (m':mem) : Prop :=
  cd=st /\ match_state st m L st' m' /\ (forall b, L b = true -> Mem.valid_block m b).

Lemma match_stackframes_sub s L s': match_stackframes s L s' -> forall L' 
        (Hs': forall b, L b = true -> L' b = true), match_stackframes s L' s'.
Proof. induction 1; simpl; intros; constructor; auto. Qed.

Lemma matchstate_extends c1 m1 L c2 m2 (MS:match_state c1 m1 L c2 m2): Mem.extends m1 m2.
Proof. inv MS; trivial. Qed.

Definition core_ord :  core_data -> core_data -> Prop:=
  fun s2 s1 => (measure s2 < measure s1)%nat.

Lemma effcore_diagram : forall st1 m1 st1' m1' (U1 : block -> Z -> bool),
effect_semantics.effstep RTL_eff_sem ge U1 st1 m1 st1' m1' -> 
forall cd st2 m2 (L : block -> bool) (MS: match_states cd st1 m1 L st2 m2),
exists
  (st2' : state) (m2' : mem) (cd' : core_data) 
(L' : block -> bool),
  L' = (fun b : block => L b || freshblock m1 m1' b) /\
  L' = (fun b : block => L b || freshblock m2 m2' b) /\
  match_states cd' st1' m1' L' st2' m2' /\
  (exists U2 : block -> Z -> bool,
     (effect_semantics.effstep_plus RTL_eff_sem tge U2
        st2 m2 st2' m2' \/
      effect_semantics.effstep_star RTL_eff_sem tge U2
        st2 m2 st2' m2' /\ core_ord cd' cd) /\
     (forall (b : block) (ofs : Z),
      U2 b ofs = true -> L b = true \/ U1 b ofs = true)).
Proof.
  induction 1; intros; destruct MS as [CD [MS HL]]; subst cd; inv MS; EliminatedInstr.

- (* nop *)
  TransfInstr.
  (*new:*) eexists; exists m2; eexists; eexists. do 2 rewrite fresh_no_alloc. 
           split. reflexivity.
           split. reflexivity.
           split. split. reflexivity. intuition. econstructor; eassumption.
           exists (fun _ _ => false).
           split. left. apply effect_semantics.effstep_plus_one. 
                  eapply effexec_Inop; eauto.
           discriminate.
- (* eliminated nop *)
  assert (s0 = pc') by congruence. subst s0.
  (*new:*) rename sp0 into sp.
           eexists; exists m2; eexists; eexists. do 2 rewrite fresh_no_alloc.
           split. reflexivity.
           split. reflexivity.
           split. split. reflexivity. intuition. econstructor; eassumption. 
           exists (fun _ _ => false).
           split. right. split. apply effect_semantics.effstep_star_zero.
                  unfold core_ord. simpl. omega.
           discriminate.
- (* op *)
  TransfInstr.
  assert (Val.lessdef_list (rs##args) (rs'##args)). apply regs_lessdef_regs; auto.
  exploit eval_operation_lessdef; eauto.
  intros [v' [EVAL' VLD]].
  exists (State s' (transf_function f) (Vptr sp0 Int.zero) pc' (rs'#res <- v')).
  exists m2; eexists; eexists. do 2 rewrite fresh_no_alloc.
  split. reflexivity.
  split. reflexivity.
  split. split. reflexivity. intuition. econstructor; try eassumption. apply set_reg_lessdef; auto.
  exists (fun _ _ => false).
  split. left. apply effect_semantics.effstep_plus_one. 
               eapply effexec_Iop; eauto.  rewrite <- EVAL'.
               apply eval_operation_preserved. exact symbols_preserved.
  discriminate. 
- (* eliminated move *)
  rewrite H1 in H. clear H1. inv H. rename sp0 into sp.
  eexists; exists m2, (State s f (Vptr sp Int.zero) pc' rs # res <- v), L. do 2 rewrite fresh_no_alloc.
  split. reflexivity.
  split. reflexivity.
  split. split; trivial. intuition. 
  Focus 2. exists (fun _ _  => false).
                  split. right. split. apply effect_semantics.effstep_star_zero.
                  unfold core_ord. simpl. omega.
                  discriminate. 
  econstructor; eauto. simpl in H0. rewrite PMap.gss. congruence.
- (* load *)
  TransfInstr.
  assert (Val.lessdef_list (rs##args) (rs'##args)). apply regs_lessdef_regs; auto.
  exploit eval_addressing_lessdef; eauto.
  intros [a' [ADDR' ALD]].
  exploit Mem.loadv_extends; eauto.
  intros [v' [LOAD' VLD]].
  exists (State s' (transf_function f) (Vptr sp0 Int.zero) pc' (rs'#dst <- v')), m2.
  eexists; exists L.  do 2 rewrite fresh_no_alloc.
  split. reflexivity.
  split. reflexivity.
  split. split. reflexivity. intuition. econstructor; eauto. apply set_reg_lessdef; auto.
  exists (fun _ _  => false).
  split. left. apply effect_semantics.effstep_plus_one. 
         eapply effexec_Iload with (a := a'). eauto.  rewrite <- ADDR'.
         apply eval_addressing_preserved. exact symbols_preserved. eauto.
  discriminate. 
- (* store *)
  TransfInstr.
  assert (Val.lessdef_list (rs##args) (rs'##args)). apply regs_lessdef_regs; auto.
  exploit eval_addressing_lessdef; eauto.
  intros [a' [ADDR' ALD]].
  exploit Mem.storev_extends. 2: eexact H1. eauto. eauto. apply RLD.
  intros [m'1 [STORE' MLD']].
  exists (State s' (transf_function f) (Vptr sp0 Int.zero) pc' rs'), m'1.
  eexists; exists L. repeat erewrite freshblock_storev, orb_false_r_ext; try eassumption.
  split. reflexivity.
  split. reflexivity.
  split. destruct a; inv H1. destruct a'; inv STORE'.
         split. reflexivity. 
         split. econstructor; eauto.
         intros. eapply Mem.store_valid_block_1; eauto.
         (*split; eapply mem_respects_readonly_fwd; eauto. eapply store_forward; eauto.
                 intros. eapply store_readonly; eauto.
                eapply store_forward; eauto.
                 intros. eapply store_readonly; eauto.*)
  eexists.
  split. left. apply effect_semantics.effstep_plus_one. 
         eapply effexec_Istore with (a := a'). eauto.  rewrite <- ADDR'.
         apply eval_addressing_preserved. exact symbols_preserved. eauto.
  clear - H1 ALD. eapply StoreEffect_propagate_ext; eauto.
- (* call *)
  exploit find_function_translated; eauto. intro FIND'.
  TransfInstr.
+ (* call turned tailcall *)
  assert ({ m2' | Mem.free m2 sp0 0 (fn_stacksize (transf_function f)) = Some m2'}).
    apply Mem.range_perm_free. rewrite stacksize_preserved. rewrite H7.
    red; intros; omegaContradiction.
  destruct X as [m2' FREE].
  exists (Callstate s' (transf_fundef fd) (rs'##args)), m2'. erewrite fresh_no_alloc, freshblock_free, orb_false_r_ext; try eassumption.
  eexists; eexists.
  split. reflexivity.
  split. reflexivity.
  split. split. reflexivity. intuition.
         constructor. eapply match_stackframes_tail; eauto. apply regs_lessdef_regs; auto.
         eapply Mem.free_right_extends; eauto.
         rewrite stacksize_preserved. rewrite H7. intros. omegaContradiction.
         (*eapply mem_respects_readonly_fwd; eauto. eapply free_forward; eauto.
                 intros. eapply free_readonly; eauto.*)
  eexists. 
  split. left. apply effect_semantics.effstep_plus_one.
               eapply effexec_Itailcall; eauto. apply sig_preserved.
  intros. apply effect_semantics.FreeEffectD in H1. destruct H1 as [FE1 [FE2 FE3]]; subst sp0.
          left; trivial.
+ (* call that remains a call *)
  exists (Callstate (Stackframe res (transf_function f) (Vptr sp0 Int.zero) pc' rs' :: s')
                          (transf_fundef fd) (rs'##args)), m2. do 2 rewrite fresh_no_alloc.
  eexists; eexists.
  split. reflexivity.
  split. reflexivity.
  split. split. reflexivity. intuition. 
         constructor. constructor; auto. apply regs_lessdef_regs; auto. auto.
  eexists.
  split. left. apply effect_semantics.effstep_plus_one.
               eapply effexec_Icall; eauto. apply sig_preserved.
  intros. right; trivial. 

- (* tailcall *)
  exploit find_function_translated; eauto. intro FIND'.
  exploit Mem.free_parallel_extends; eauto. intros [m2' [FREE EXT]].
  TransfInstr.
  exists (Callstate s' (transf_fundef fd) (rs'##args)), m2'; eexists; eexists.
  erewrite freshblock_free, orb_false_r_ext; try eassumption.
  erewrite freshblock_free, orb_false_r_ext; try eassumption.
  split. reflexivity.
  split. reflexivity.
  split. split. reflexivity. intuition.
         constructor. auto. apply regs_lessdef_regs; auto. auto.
         eapply Mem.valid_block_free_1; eauto. 
         (*eapply mem_respects_readonly_fwd; eauto. eapply free_forward; eauto.
                 intros. eapply free_readonly; eauto.
         eapply mem_respects_readonly_fwd; eauto. eapply free_forward; eauto.
                 intros. eapply free_readonly; eauto.*)
  eexists.
  split. left. apply effect_semantics.effstep_plus_one.
         eapply effexec_Itailcall; eauto. apply sig_preserved.
         rewrite stacksize_preserved; auto.
  intros. apply effect_semantics.FreeEffectD in H1. destruct H1 as [FE1 [FE2 FE3]]; subst stk.
          left; trivial.
- (* builtin *)
  TransfInstr.
  exploit (@eval_builtin_args_lessdef _ ge (fun r => rs#r) (fun r => rs'#r)); eauto.
  intros (vargs' & P & Q).
  exploit (nonobservables_mem_extends ge tge); eauto.
  intros [v' [m2' [A [B [C D]]]]].
  exists (State s' (transf_function f) (Vptr sp0 Int.zero) pc' (regmap_setres res v' rs')), m2'; eexists; eexists.
  split. reflexivity. 
  split. rewrite (extends_extends_freshblock _ _ _ _ MLD C); trivial. 
  split. { split. reflexivity.
           apply external_call_mem_forward in H1; apply external_call_mem_forward in A;
           split. 
           { econstructor; eauto.    
             eapply match_stackframes_sub; eauto. intros b Hb; rewrite Hb; trivial.
             apply set_res_lessdef; auto.
             rewrite Lsp; trivial. }
           { intros b Hb. remember (L b) as q; destruct q; simpl in *; symmetry in Heqq.
                   apply H1; eauto.
                   apply freshblockProp_char in Hb; eapply Hb. } }
  eexists.
  split. left. apply effect_semantics.effstep_plus_one.
         eapply effexec_Ibuiltin; eauto.
         eapply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
         (*eapply external_call_symbols_preserved; eauto. apply senv_preserved.*)
  intros. right. eapply BuiltinEffects_propagate_extends; eassumption. 

- (* cond *)
  TransfInstr.
  exists (State s' (transf_function f) (Vptr sp0 Int.zero) (if b then ifso else ifnot) rs'), m2.
  do 2 rewrite fresh_no_alloc.
  eexists; eexists.
  split. reflexivity.
  split. reflexivity.
  split. split. reflexivity. split; trivial. 
         constructor; auto.
  eexists.
  split. left. apply effect_semantics.effstep_plus_one.
         eapply effexec_Icond; eauto.
         apply eval_condition_lessdef with (rs##args) m; auto. apply regs_lessdef_regs; auto.
  intros; right; trivial. 

- (* jumptable *)
  TransfInstr.
  exists (State s' (transf_function f) (Vptr sp0 Int.zero) pc' rs'), m2. 
  do 2 rewrite fresh_no_alloc.
  eexists; eexists.
  split. reflexivity.
  split. reflexivity.
  split. split. reflexivity. split; trivial. 
         constructor; auto.
  eexists.
  split. left. apply effect_semantics.effstep_plus_one.
         eapply effexec_Ijumptable; eauto.
         generalize (RLD arg). rewrite H0. intro. inv H2. auto.
  intros; right; trivial. 

- (* return *)
  exploit Mem.free_parallel_extends; eauto. intros [m2' [FREE EXT]].
  TransfInstr.
  exists (Returnstate s' (regmap_optget or Vundef rs')), m2'. 
  erewrite freshblock_free, orb_false_r_ext; try eassumption.
  erewrite freshblock_free, orb_false_r_ext; try eassumption.
  eexists; eexists.
  split. reflexivity.
  split. reflexivity.
  split. split. reflexivity.
         split. constructor; auto.
                destruct or; simpl. apply RLD. constructor.
         intros. eapply Mem.valid_block_free_1; eauto. 
  eexists.
  split. left. apply effect_semantics.effstep_plus_one.
         apply effexec_Ireturn; auto. rewrite stacksize_preserved; auto.
  intros. apply effect_semantics.FreeEffectD in H1. destruct H1 as [FE1 [FE2 FE3]]; subst stk.
          left; trivial.

- (* eliminated return None *)
  assert (or = None) by congruence. subst or.
  eexists (Returnstate s' v'), m2; eexists; eexists.
  rewrite fresh_no_alloc.
  erewrite freshblock_free, orb_false_r_ext; try eassumption.
  split. reflexivity.
  split. reflexivity.
  split. split. reflexivity.
         split. simpl. constructor; try eassumption. constructor.
                eapply Mem.free_left_extends; eauto.
         intros. eapply Mem.valid_block_free_1; eauto. 
  eexists.
  split. right. split. apply effect_semantics.effstep_star_zero.
                unfold core_ord. simpl. omega.
  discriminate. 

- (* eliminated return Some *)
  assert (or = Some r) by congruence. subst or.
  eexists (Returnstate s' v'), m2; eexists; eexists.
  rewrite fresh_no_alloc.
  erewrite freshblock_free, orb_false_r_ext; try eassumption.
  split. reflexivity.
  split. reflexivity.
  split. split. reflexivity.
         split. simpl. constructor; try eassumption.  
                eapply Mem.free_left_extends; eauto.
         intros. eapply Mem.valid_block_free_1; eauto. 
  eexists.
  split. right. split. apply effect_semantics.effstep_star_zero.
                unfold core_ord. simpl. omega.
  discriminate. 

- (* internal call *)
  exploit Mem.alloc_extends; eauto.
    instantiate (1 := 0). omega.
    instantiate (1 := fn_stacksize f). omega.
  intros [m2' [ALLOC EXT]].
  assert (fn_stacksize (transf_function f) = fn_stacksize f /\
          fn_entrypoint (transf_function f) = fn_entrypoint f /\
          fn_params (transf_function f) = fn_params f).
    unfold transf_function. destruct (zeq (fn_stacksize f) 0); auto.
  destruct H0 as [EQ1 [EQ2 EQ3]]. 
  exists (State s' (transf_function f) (Vptr stk Int.zero) (fn_entrypoint (transf_function f))
            (init_regs args' (fn_params (transf_function f)))), m2'.
  eexists; eexists.
  erewrite freshblock_alloc; try eassumption.
  erewrite freshblock_alloc; try eassumption.
  split. reflexivity.
  split. reflexivity.
  split. split. reflexivity.
         split. rewrite EQ2. rewrite EQ3. constructor; auto. 
                eapply match_stackframes_sub; try eassumption. intros b Hb; rewrite Hb; reflexivity. 
                apply regs_lessdef_init_regs. auto.
                destruct (eq_block stk stk); simpl. apply orb_true_r. congruence.
         intros. apply orb_true_iff in H0. destruct H0.
                 eapply Mem.valid_block_alloc; eauto.
                 destruct (eq_block stk b); inv H0.
                 eapply Mem.valid_new_block; eassumption. 
  eexists. split. left. apply effect_semantics.effstep_plus_one.
           eapply effexec_function_internal; eauto. rewrite EQ1; eauto.
  discriminate.

- (* external call - COMPCOMP: now restricted to helper functions*)
  specialize (EFhelpers _ OBS); intros.
  exploit (nonobservables_mem_extends ge tge); eauto.
  intros [res' [m2' [A [B [C D]]]]].
  exists (Returnstate s' res'), m2'. eexists; eexists.
  split. reflexivity. 
  split. rewrite (extends_extends_freshblock _ _ _ _ H9 C); trivial.
  split. { split. reflexivity.
           split. econstructor; eauto.   
           eapply match_stackframes_sub; eauto. intros b Hb; rewrite Hb; trivial.
           intros b Hb. remember (L b) as q; destruct q; simpl in *; symmetry in Heqq.
                   eapply external_call_mem_forward; eauto.
                   apply freshblockProp_char in Hb; eapply Hb. }
  eexists.
  split. left. apply effect_semantics.effstep_plus_one.
         econstructor; eauto.
         (*eapply external_call_symbols_preserved; eauto. apply senv_preserved.*)
  intros. right. eapply BuiltinEffects_propagate_extends; eassumption. 

- (* returnstate *)
  inv H1.
+ (* synchronous return in both programs *)
  exists (State stk' (transf_function f) (Vptr sp0 Int.zero) pc rs' # res <- v'), m2; eexists; eexists.
  rewrite fresh_no_alloc.
  rewrite fresh_no_alloc.
  split. reflexivity.
  split. reflexivity.
  split. split. reflexivity. split; trivial.
                econstructor; eauto. apply set_reg_lessdef; auto.
  eexists.
  split. left. apply effect_semantics.effstep_plus_one.
         apply effexec_return.
  intros. right; trivial.
+ (* return instr in source program, eliminated because of tailcall *)
  exists (Returnstate s' v'), m2; eexists; eexists.
  rewrite fresh_no_alloc.
  rewrite fresh_no_alloc.
  split. reflexivity.
  split. reflexivity.
  split. split. reflexivity. split; trivial. 
         econstructor; eauto. rewrite Regmap.gss. auto.
  eexists.
  split. right. split. apply effect_semantics.effstep_star_zero.
         unfold core_ord. unfold measure. simpl length.
         change (S (length s) * (niter + 2))%nat
            with ((niter + 2) + (length s) * (niter + 2))%nat.
         generalize (return_measure_bounds (fn_code f) pc). omega.
  discriminate. 
Qed.

Require Import sepcomp.effect_semantics.

Definition SIM: Mini_simulation_ext.Mini_simulation_extend RTL_eff_sem RTL_eff_sem ge tge.
econstructor.
+ apply well_founded_ltof. 
+ split. apply senv_preserved.
  red. unfold ge, tge. admit. (*maybe using isGlobalBlock is more prudent?*) 
+ instantiate (1:= fun d c1 m1 L c2 m2 => match_states d c1 m1 L c2 m2 /\
      mem_respects_readonly ge m1 /\ mem_respects_readonly tge m2).
  intros. destruct H as [[? [MS ?]] [MRSrc MRTgt]]; subst.
  apply matchstate_extends in MS. apply H1 in H0. split; trivial.
  eapply (Mem.valid_block_extends m1); eassumption. 
+ intros. destruct H as [[? [MS ?]][MRSrc MRTgt]]; subst.
  apply matchstate_extends in MS. apply Mem.valid_block_extends; trivial. 
+ admit. (*genv stuff*)
+ (*initialCore*)
  intros. simpl in *. destruct v; inv H; simpl.
  destruct (Int.eq_dec i Int.zero); inv H7.
  remember (Genv.find_funct_ptr ge b) as q; symmetry in Heqq; destruct q; inv H6.
  apply funct_ptr_translated in Heqq. rewrite Heqq.
  destruct f; inv H7. simpl.
  rewrite <- (mem_lemmas.Forall2_Zlength H0).
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
      end Int.max_unsigned); inv H6.
  eexists; eexists; split. reflexivity.
  split. split. reflexivity.
         split. constructor; eauto. constructor. apply mem_lemmas.forall_lessdef_val_listless; trivial.
         discriminate.
  split; trivial.
+ (*CoreDiagram*)
  intros. destruct H0 as [MS [MRSrc MRTgt]]; subst.
  exploit effcore_diagram; eauto. intros [st2' [m2' [cd' [L' [HL1' [HL2' [MS' HU]]]]]]].
  exists st2', m2', cd', L'. intuition.
  - exploit semantics_lemmas.mem_step_readonly. eapply effstep_mem. apply H.
    intros [Fwd RD]. eapply mem_respects_readonly_fwd; eauto.
  - destruct HU as [U2 [HU _]].
    exploit semantics_lemmas.mem_step_readonly.
      destruct HU. eapply effstep_plus_mem; eauto. eapply effstep_star_mem; eapply a. 
    intros [Fwd RD]. eapply mem_respects_readonly_fwd; eauto.
  - apply HU. 
+ (*Halted*)
  intros. destruct st1; inv H0. destruct stack; inv H2. destruct H as [[? [MS HL]] [MRRsrc MRRTgt]]; subst.
  inv MS. inv H1. 
  exists v'. intuition. 
+ (*atExternal*)
  intros. destruct st1; inv H0. destruct f; inv H2. destruct (observableEF_dec e0); inv H1.
  destruct H as [[? [MS HL]][MRRsrc MRRTgt]]; subst. inv MS. intuition.
  exists args'. split. apply mem_lemmas.val_listless_forall_lessdef; eassumption.
  simpl. destruct (observableEF_dec e); trivial. contradiction.
+ (*afterExternal*)
  intros. destruct st1; inv AtExtSrc. destruct f; inv H0. destruct (observableEF_dec e0); inv H1.
  destruct MatchMu as [[? [MS HL]] [MRRsrc MRRTgt]]; subst. inv MS. simpl in *.
  destruct (observableEF_dec e); try solve [contradiction]. inv AtExtTgt.
  eexists; eexists; eexists. split. reflexivity. split. reflexivity.
  split. split. reflexivity. 
         split. econstructor; trivial.
         intros. apply FwdSrc; eauto.
  split; eapply mem_respects_readonly_forward'; eassumption. 
Admitted.

(** The preservation of the observable behavior of the program then
  follows. *)

Require Import minisepcomp.transEI.
Definition SIMj: Mini_simulation_inj.Mini_simulation_inject RTL_eff_sem RTL_eff_sem ge tge.
eapply EI_sim_trans.
apply SIM.
admit. (*TODO: RTL selfinjects*)
Admitted.

End PRESERVATION.

