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

(** The RTL intermediate language: abstract syntax and semantics.

  RTL stands for "Register Transfer Language". This is the first
  intermediate language after Cminor and CminorSel.
*)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Events.
Require Import Memory.
Require Import Globalenvs.
(*Require Import Smallstep.*)
Require Import minisepcomp.Op.
Require Import minisepcomp.Registers.
Require Import minisepcomp.BuiltinEffects.


(** * Abstract syntax *)

(** RTL is organized as instructions, functions and programs.
  Instructions correspond roughly to elementary instructions of the
  target processor, but take their arguments and leave their results
  in pseudo-registers (also called temporaries in textbooks).
  Infinitely many pseudo-registers are available, and each function
  has its own set of pseudo-registers, unaffected by function calls.

  Instructions are organized as a control-flow graph: a function is
  a finite map from ``nodes'' (abstract program points) to instructions,
  and each instruction lists explicitly the nodes of its successors.
*)

Definition node := positive.

Inductive instruction: Type :=
  | Inop: node -> instruction
      (** No operation -- just branch to the successor. *)
  | Iop: operation -> list reg -> reg -> node -> instruction
      (** [Iop op args dest succ] performs the arithmetic operation [op]
          over the values of registers [args], stores the result in [dest],
          and branches to [succ]. *)
  | Iload: memory_chunk -> addressing -> list reg -> reg -> node -> instruction
      (** [Iload chunk addr args dest succ] loads a [chunk] quantity from
          the address determined by the addressing mode [addr] and the
          values of the [args] registers, stores the quantity just read
          into [dest], and branches to [succ]. *)
  | Istore: memory_chunk -> addressing -> list reg -> reg -> node -> instruction
      (** [Istore chunk addr args src succ] stores the value of register
          [src] in the [chunk] quantity at the
          the address determined by the addressing mode [addr] and the
          values of the [args] registers, then branches to [succ]. *)
  | Icall: signature -> reg + ident -> list reg -> reg -> node -> instruction
      (** [Icall sig fn args dest succ] invokes the function determined by
          [fn] (either a function pointer found in a register or a
          function name), giving it the values of registers [args]
          as arguments.  It stores the return value in [dest] and branches
          to [succ]. *)
  | Itailcall: signature -> reg + ident -> list reg -> instruction
      (** [Itailcall sig fn args] performs a function invocation
          in tail-call position.  *)
  | Ibuiltin: external_function -> list (builtin_arg reg) -> builtin_res reg -> node -> instruction
      (** [Ibuiltin ef args dest succ] calls the built-in function
          identified by [ef], giving it the values of [args] as arguments.
          It stores the return value in [dest] and branches to [succ]. *)
  | Icond: condition -> list reg -> node -> node -> instruction
      (** [Icond cond args ifso ifnot] evaluates the boolean condition
          [cond] over the values of registers [args].  If the condition
          is true, it transitions to [ifso].  If the condition is false,
          it transitions to [ifnot]. *)
  | Ijumptable: reg -> list node -> instruction
      (** [Ijumptable arg tbl] transitions to the node that is the [n]-th
          element of the list [tbl], where [n] is the signed integer
          value of register [arg]. *)
  | Ireturn: option reg -> instruction.
      (** [Ireturn] terminates the execution of the current function
          (it has no successor).  It returns the value of the given
          register, or [Vundef] if none is given. *)

Definition code: Type := PTree.t instruction.

Record function: Type := mkfunction {
  fn_sig: signature;
  fn_params: list reg;
  fn_stacksize: Z;
  fn_code: code;
  fn_entrypoint: node
}.

(** A function description comprises a control-flow graph (CFG) [fn_code]
    (a partial finite mapping from nodes to instructions).  As in Cminor,
    [fn_sig] is the function signature and [fn_stacksize] the number of bytes
    for its stack-allocated activation record.  [fn_params] is the list
    of registers that are bound to the values of arguments at call time.
    [fn_entrypoint] is the node of the first instruction of the function
    in the CFG. *)

Definition fundef := AST.fundef function.

Definition program := AST.program fundef unit.

Definition funsig (fd: fundef) :=
  match fd with
  | Internal f => fn_sig f
  | External ef => ef_sig ef
  end.

(** * Operational semantics *)

Definition genv := Genv.t fundef unit.
Definition regset := Regmap.t val.

Fixpoint init_regs (vl: list val) (rl: list reg) {struct rl} : regset :=
  match rl, vl with
  | r1 :: rs, v1 :: vs => Regmap.set r1 v1 (init_regs vs rs)
  | _, _ => Regmap.init Vundef
  end.

(** The dynamic semantics of RTL is given in small-step style, as a
  set of transitions between states.  A state captures the current
  point in the execution.  Three kinds of states appear in the transitions:

- [State cs f sp pc rs m] describes an execution point within a function.
  [f] is the current function.
  [sp] is the pointer to the stack block for its current activation
     (as in Cminor).
  [pc] is the current program point (CFG node) within the code [c].
  [rs] gives the current values for the pseudo-registers.
  [m] is the current memory state.
- [Callstate cs f args m] is an intermediate state that appears during
  function calls.
  [f] is the function definition that we are calling.
  [args] (a list of values) are the arguments for this call.
  [m] is the current memory state.
- [Returnstate cs v m] is an intermediate state that appears when a
  function terminates and returns to its caller.
  [v] is the return value and [m] the current memory state.

In all three kinds of states, the [cs] parameter represents the call stack.
It is a list of frames [Stackframe res f sp pc rs].  Each frame represents
a function call in progress.
[res] is the pseudo-register that will receive the result of the call.
[f] is the calling function.
[sp] is its stack pointer.
[pc] is the program point for the instruction that follows the call.
[rs] is the state of registers in the calling function.
*)

Inductive stackframe : Type :=
  | Stackframe:
      forall (res: reg)            (**r where to store the result *)
             (f: function)         (**r calling function *)
             (sp: val)             (**r stack pointer in calling function *)
             (pc: node)            (**r program point in calling function *)
             (rs: regset),         (**r register state in calling function *)
      stackframe.

(*COMPCOMP adaptation: remove mem components in all 3 constructors*)
Inductive state : Type :=
  | State:
      forall (stack: list stackframe) (**r call stack *)
             (f: function)            (**r current function *)
             (sp: val)                (**r stack pointer *)
             (pc: node)               (**r current program point in [c] *)
             (rs: regset),            (**r register state *)
      state
  | Callstate:
      forall (stack: list stackframe) (**r call stack *)
             (f: fundef)              (**r function to call *)
             (args: list val),        (**r arguments to the call *)
      state
  | Returnstate:
      forall (stack: list stackframe) (**r call stack *)
             (v: val),                (**r return value for the call *)
      state.

Section RELSEM.

Variable ge: genv.

Definition find_function
      (ros: reg + ident) (rs: regset) : option fundef :=
  match ros with
  | inl r => Genv.find_funct ge rs#r
  | inr symb =>
      match Genv.find_symbol ge symb with
      | None => None
      | Some b => Genv.find_funct_ptr ge b
      end
  end.

(** The transitions are presented as an inductive predicate
  [step ge st1 t st2], where [ge] is the global environment,
  [st1] the initial state, [st2] the final state. *)

(*COMPCOMP adaptation: Old type: Inductive step: state -> trace -> state -> Prop :=*)
Inductive step: state -> mem -> state -> mem -> Prop :=
  | exec_Inop:
      forall s f sp pc rs m pc',
      (fn_code f)!pc = Some(Inop pc') ->
      step (State s f sp pc rs) m
        (*E0*) (State s f sp pc' rs) m
  | exec_Iop:
      forall s f sp pc rs m op args res pc' v,
      (fn_code f)!pc = Some(Iop op args res pc') ->
      eval_operation ge sp op rs##args m = Some v ->
      step (State s f sp pc rs) m
        (*E0*) (State s f sp pc' (rs#res <- v)) m
  | exec_Iload:
      forall s f sp pc rs m chunk addr args dst pc' a v,
      (fn_code f)!pc = Some(Iload chunk addr args dst pc') ->
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.loadv chunk m a = Some v ->
      step (State s f sp pc rs) m
        (*E0*) (State s f sp pc' (rs#dst <- v)) m
  | exec_Istore:
      forall s f sp pc rs m chunk addr args src pc' a m',
      (fn_code f)!pc = Some(Istore chunk addr args src pc') ->
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.storev chunk m a rs#src = Some m' ->
      step (State s f sp pc rs) m
        (*E0*) (State s f sp pc' rs) m'
  | exec_Icall:
      forall s f sp pc rs m sig ros args res pc' fd,
      (fn_code f)!pc = Some(Icall sig ros args res pc') ->
      find_function ros rs = Some fd ->
      funsig fd = sig ->
      step (State s f sp pc rs) m
        (*E0*) (Callstate (Stackframe res f sp pc' rs :: s) fd rs##args) m
  | exec_Itailcall:
      forall s f stk pc rs m sig ros args fd m',
      (fn_code f)!pc = Some(Itailcall sig ros args) ->
      find_function ros rs = Some fd ->
      funsig fd = sig ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      step (State s f (Vptr stk Int.zero) pc rs) m
        (*E0*) (Callstate s fd rs##args) m'
  | exec_Ibuiltin:
      forall s f sp pc rs m ef args res pc' vargs t vres m',
      (fn_code f)!pc = Some(Ibuiltin ef args res pc') ->
      eval_builtin_args ge (fun r => rs#r) sp m args vargs ->
      external_call ef ge vargs m t vres m' ->
      (*COMPCOMP adaptation: limit to unobervables:*) ~ observableEF (*hf*) ef ->
      step (State s f sp pc rs) m
         (*t*) (State s f sp pc' (regmap_setres res vres rs)) m'
  | exec_Icond:
      forall s f sp pc rs m cond args ifso ifnot b pc',
      (fn_code f)!pc = Some(Icond cond args ifso ifnot) ->
      eval_condition cond rs##args m = Some b ->
      pc' = (if b then ifso else ifnot) ->
      step (State s f sp pc rs) m
        (*E0*) (State s f sp pc' rs) m
  | exec_Ijumptable:
      forall s f sp pc rs m arg tbl n pc',
      (fn_code f)!pc = Some(Ijumptable arg tbl) ->
      rs#arg = Vint n ->
      list_nth_z tbl (Int.unsigned n) = Some pc' ->
      step (State s f sp pc rs) m
        (*E0*) (State s f sp pc' rs) m
  | exec_Ireturn:
      forall s f stk pc rs m or m',
      (fn_code f)!pc = Some(Ireturn or) ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      step (State s f (Vptr stk Int.zero) pc rs) m
        (*E0*) (Returnstate s (regmap_optget or Vundef rs)) m'
  | exec_function_internal:
      forall s f args m m' stk,
      Mem.alloc m 0 f.(fn_stacksize) = (m', stk) ->
      step (Callstate s (Internal f) args) m
        (*E0*) (State s
                  f
                  (Vptr stk Int.zero)
                  f.(fn_entrypoint)
                  (init_regs args f.(fn_params)))
                  m'
  | exec_function_external:
      forall s ef args res t m m'
      (*COMPCOMP adaptation: restrict to helper functions*)(OBS: EFisHelper (*hf*) ef),
      external_call ef ge args m t res m' ->
      step (Callstate s (External ef) args) m
         (*t*) (Returnstate s res) m'
  | exec_return:
      forall res f sp pc rs s vres m,
      step (Returnstate (Stackframe res f sp pc rs :: s) vres) m
        (*E0*) (State s f sp pc (rs#res <- vres)) m.

Lemma exec_Iop':
  forall s f sp pc rs m op args res pc' rs' v,
  (fn_code f)!pc = Some(Iop op args res pc') ->
  eval_operation ge sp op rs##args m = Some v ->
  rs' = (rs#res <- v) ->
  step (State s f sp pc rs) m
    (*E0*) (State s f sp pc' rs') m.
Proof.
  intros. subst rs'. eapply exec_Iop; eauto.
Qed.

Lemma exec_Iload':
  forall s f sp pc rs m chunk addr args dst pc' rs' a v,
  (fn_code f)!pc = Some(Iload chunk addr args dst pc') ->
  eval_addressing ge sp addr rs##args = Some a ->
  Mem.loadv chunk m a = Some v ->
  rs' = (rs#dst <- v) ->
  step (State s f sp pc rs) m
    (*E0*) (State s f sp pc' rs') m.
Proof.
  intros. subst rs'. eapply exec_Iload; eauto.
Qed.

End RELSEM.

(** Execution of whole programs are described as sequences of transitions
  from an initial state to a final state.  An initial state is a [Callstate]
  corresponding to the invocation of the ``main'' function of the program
  without arguments and with an empty call stack. *)

(*COMPCOMP adaptation: replaced by RTL_initial_core, which in particular drops the
  assumption that m be init_mem
Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall b f m0,
      let ge := Genv.globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      funsig f = signature_main ->
      initial_state p (Callstate nil f nil m0).*)

(*LENB: TODO: reactivate val_has_type_list_func args (sig_args (funsig f))
                    && vals_defined args
  by copying suitable files from CompComp2.1*)
Definition RTL_initial_core (ge: genv) (v:val)(args: list val): option state:=
  match v with
    | Vptr b i =>
      if Int.eq_dec i Int.zero
      then match Genv.find_funct_ptr ge b with
             | None => None
             | Some f => 
               match f with Internal fi =>
                 let tyl := sig_args (funsig f) in
                 if (*val_has_type_list_func args (sig_args (funsig f))
                    && vals_defined args
                    &&*) zlt (4*(2*(Zlength args))) Int.max_unsigned
                 then Some (Callstate nil f args)
                 else None
               | External _ => None
               end
           end
      else None
    | _ => None
  end.


(** A final state is a [Returnstate] with an empty call stack. *)

(*COMPCOMP adaptation: replaced by RTL_halted, which in particular drops the
  requirement that return values be integers
Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall r m,
      final_state (Returnstate nil (Vint r) m) r.*)
Definition RTL_halted (c: state ): option val :=
  match c with
      Returnstate nil v => Some v
    | _ => None
  end.

(*COMPCOMP adaptation: removed - maybe reactivate/adapt later?
(** The small-step semantics for a program. *)

Definition semantics (p: program) :=
  Semantics step (initial_state p) final_state (Genv.globalenv p).

(** This semantics is receptive to changes in events. *)

Lemma semantics_receptive:
  forall (p: program), receptive (semantics p).
Proof.
  intros. constructor; simpl; intros.
(* receptiveness *)
  assert (t1 = E0 -> exists s2, step (Genv.globalenv p) s t2 s2).
    intros. subst. inv H0. exists s1; auto.
  inversion H; subst; auto.
  exploit external_call_receptive; eauto. intros [vres2 [m2 EC2]].
  exists (State s0 f sp pc' (regmap_setres res vres2 rs) m2). eapply exec_Ibuiltin; eauto.
  exploit external_call_receptive; eauto. intros [vres2 [m2 EC2]].
  exists (Returnstate s0 vres2 m2). econstructor; eauto.
(* trace length *)
  red; intros; inv H; simpl; try omega.
  eapply external_call_trace_length; eauto.
  eapply external_call_trace_length; eauto.
Qed.
*)

(** COMPCOMP NEW SECTION: Building a MemSem semantics *)
Require Import sepcomp.semantics.
Require Import sepcomp.semantics_lemmas.

Definition RTL_at_external (c: state): option (external_function * signature * list val) :=
  match c with
    | State stack f sp pc rs => None
    | Callstate stack f args => 
        match f with
          Internal _ => None
        | External ef =>  if observableEF_dec (*hf*) ef 
                          then Some(ef, ef_sig ef, args)
                          else None
        end
    | Returnstate stack v => None
  end.

Definition RTL_after_external (vret: option val)(c: state): option state :=
  match c with
    | State stack f sp pc rs => None
    | Callstate stack f args => 
      match f with
          Internal _ => None
        | External f' => match vret with
                             None => Some (Returnstate stack Vundef)
                           | Some v => Some (Returnstate stack v)
                         end
      end
    | Returnstate stack v => None
  end.           

Lemma rtl_step_not_external: forall (ge : genv) m q m' q',
                               step ge q m q' m' -> RTL_at_external q = None.
Proof.
  intros. inv H; try reflexivity. 
  simpl. destruct (observableEF_dec (*hf*) ef); simpl; trivial. 
  eelim EFhelpers; eassumption. 
Qed.

Lemma rtl_step_not_halted: forall (ge : genv) m q m' q',
                           step ge q m q' m' -> RTL_halted q = None.
Proof. intros. inv H; try reflexivity. Qed.

Lemma rtl_external_xor_halted: forall q, RTL_at_external q = None \/ RTL_halted q = None.
Proof.
  destruct q; simpl; try (left; reflexivity); try (right; reflexivity).
Qed.

Lemma rtl_after_xor_at_external: forall (retv : option val) q q',
                               RTL_after_external retv q = Some q' -> RTL_at_external q' = None.
Proof.
  intros. destruct q; destruct q'; try destruct f; destruct retv; simpl in *; try discriminate; try reflexivity.
Qed.

Definition RTL_core_sem : CoreSemantics genv state mem.
Proof.
  eapply (@Build_CoreSemantics _ _ _ 
            RTL_initial_core
            RTL_at_external
            RTL_after_external
            RTL_halted
            step).
  apply rtl_step_not_external.
  apply rtl_step_not_halted. 
  apply rtl_external_xor_halted.
Defined.

Lemma rtl_step_mem : forall g c m c' m' (CS: step g c m c' m'), mem_step m m'.
Proof. intros.
       inv CS; try apply mem_step_refl.
       + (*Storev*)
          destruct a; simpl in H1; inv H1. 
          eapply mem_step_store; eassumption.
       + (*Itailcall*)
          eapply mem_step_free; eassumption.
       + admit. (*external call to unobservable function -- needs axiom
         eapply external_call_mem_step; eassumption.*)
       + (*Ireturn*)
          eapply mem_step_free; eassumption.
       + (*alloc*)
          eapply mem_step_alloc; eassumption.
       + admit. (*external call to helper function -- needs axiom
         eapply external_call_mem_step; eassumption.*)
Admitted.

Program Definition RTL_mem_sem : MemSem genv state.
Proof.
apply Build_MemSem with (csem := RTL_core_sem).
  apply rtl_step_mem.
Defined.


(** * Operations on RTL abstract syntax *)

(** Transformation of a RTL function instruction by instruction.
  This applies a given transformation function to all instructions
  of a function and constructs a transformed function from that. *)

Section TRANSF.

Variable transf: node -> instruction -> instruction.

Definition transf_function (f: function) : function :=
  mkfunction
    f.(fn_sig)
    f.(fn_params)
    f.(fn_stacksize)
    (PTree.map transf f.(fn_code))
    f.(fn_entrypoint).

End TRANSF.

(** Computation of the possible successors of an instruction.
  This is used in particular for dataflow analyses. *)

Definition successors_instr (i: instruction) : list node :=
  match i with
  | Inop s => s :: nil
  | Iop op args res s => s :: nil
  | Iload chunk addr args dst s => s :: nil
  | Istore chunk addr args src s => s :: nil
  | Icall sig ros args res s => s :: nil
  | Itailcall sig ros args => nil
  | Ibuiltin ef args res s => s :: nil
  | Icond cond args ifso ifnot => ifso :: ifnot :: nil
  | Ijumptable arg tbl => tbl
  | Ireturn optarg => nil
  end.

Definition successors_map (f: function) : PTree.t (list node) :=
  PTree.map1 successors_instr f.(fn_code).

(** The registers used by an instruction *)

Definition instr_uses (i: instruction) : list reg :=
  match i with
  | Inop s => nil
  | Iop op args res s => args
  | Iload chunk addr args dst s => args
  | Istore chunk addr args src s => src :: args
  | Icall sig (inl r) args res s => r :: args
  | Icall sig (inr id) args res s => args
  | Itailcall sig (inl r) args => r :: args
  | Itailcall sig (inr id) args => args
  | Ibuiltin ef args res s => params_of_builtin_args args
  | Icond cond args ifso ifnot => args
  | Ijumptable arg tbl => arg :: nil
  | Ireturn None => nil
  | Ireturn (Some arg) => arg :: nil
  end.

(** The register defined by an instruction, if any *)

Definition instr_defs (i: instruction) : option reg :=
  match i with
  | Inop s => None
  | Iop op args res s => Some res
  | Iload chunk addr args dst s => Some dst
  | Istore chunk addr args src s => None
  | Icall sig ros args res s => Some res
  | Itailcall sig ros args => None
  | Ibuiltin ef args res s =>
      match res with BR r => Some r | _ => None end
  | Icond cond args ifso ifnot => None
  | Ijumptable arg tbl => None
  | Ireturn optarg => None
  end.

(** Maximum PC (node number) in the CFG of a function.  All nodes of
  the CFG of [f] are between 1 and [max_pc_function f] (inclusive). *)

Definition max_pc_function (f: function) :=
  PTree.fold (fun m pc i => Pmax m pc) f.(fn_code) 1%positive.

Lemma max_pc_function_sound:
  forall f pc i, f.(fn_code)!pc = Some i -> Ple pc (max_pc_function f).
Proof.
  intros until i. unfold max_pc_function.
  apply PTree_Properties.fold_rec with (P := fun c m => c!pc = Some i -> Ple pc m).
  (* extensionality *)
  intros. apply H0. rewrite H; auto.
  (* base case *)
  rewrite PTree.gempty. congruence.
  (* inductive case *)
  intros. rewrite PTree.gsspec in H2. destruct (peq pc k).
  inv H2. xomega.
  apply Ple_trans with a. auto. xomega.
Qed.

(** Maximum pseudo-register mentioned in a function.  All results or arguments
  of an instruction of [f], as well as all parameters of [f], are between
  1 and [max_reg_function] (inclusive). *)

Definition max_reg_instr (m: positive) (pc: node) (i: instruction) :=
  match i with
  | Inop s => m
  | Iop op args res s => fold_left Pmax args (Pmax res m)
  | Iload chunk addr args dst s => fold_left Pmax args (Pmax dst m)
  | Istore chunk addr args src s => fold_left Pmax args (Pmax src m)
  | Icall sig (inl r) args res s => fold_left Pmax args (Pmax r (Pmax res m))
  | Icall sig (inr id) args res s => fold_left Pmax args (Pmax res m)
  | Itailcall sig (inl r) args => fold_left Pmax args (Pmax r m)
  | Itailcall sig (inr id) args => fold_left Pmax args m
  | Ibuiltin ef args res s =>
      fold_left Pmax (params_of_builtin_args args)
        (fold_left Pmax (params_of_builtin_res res) m)
  | Icond cond args ifso ifnot => fold_left Pmax args m
  | Ijumptable arg tbl => Pmax arg m
  | Ireturn None => m
  | Ireturn (Some arg) => Pmax arg m
  end.

Definition max_reg_function (f: function) :=
  Pmax
    (PTree.fold max_reg_instr f.(fn_code) 1%positive)
    (fold_left Pmax f.(fn_params) 1%positive).

Remark max_reg_instr_ge:
  forall m pc i, Ple m (max_reg_instr m pc i).
Proof.
  intros.
  assert (X: forall l n, Ple m n -> Ple m (fold_left Pmax l n)).
  { induction l; simpl; intros.
    auto.
    apply IHl. xomega. }
  destruct i; simpl; try (destruct s0); repeat (apply X); try xomega.
  destruct o; xomega.
Qed.

Remark max_reg_instr_def:
  forall m pc i r, instr_defs i = Some r -> Ple r (max_reg_instr m pc i).
Proof.
  intros.
  assert (X: forall l n, Ple r n -> Ple r (fold_left Pmax l n)).
  { induction l; simpl; intros. xomega. apply IHl. xomega. }
  destruct i; simpl in *; inv H.
- apply X. xomega.
- apply X. xomega.
- destruct s0; apply X; xomega.
- destruct b; inv H1. apply X. simpl. xomega.
Qed.

Remark max_reg_instr_uses:
  forall m pc i r, In r (instr_uses i) -> Ple r (max_reg_instr m pc i).
Proof.
  intros.
  assert (X: forall l n, In r l \/ Ple r n -> Ple r (fold_left Pmax l n)).
  { induction l; simpl; intros.
    tauto.
    apply IHl. destruct H0 as [[A|A]|A]. right; subst; xomega. auto. right; xomega. }
  destruct i; simpl in *; try (destruct s0); try (apply X; auto).
- contradiction.
- destruct H. right; subst; xomega. auto.
- destruct H. right; subst; xomega. auto.
- destruct H. right; subst; xomega. auto.
- intuition. subst; xomega.
- destruct o; simpl in H; intuition. subst; xomega.
Qed.

Lemma max_reg_function_def:
  forall f pc i r,
  f.(fn_code)!pc = Some i -> instr_defs i = Some r -> Ple r (max_reg_function f).
Proof.
  intros.
  assert (Ple r (PTree.fold max_reg_instr f.(fn_code) 1%positive)).
  {  revert H.
     apply PTree_Properties.fold_rec with
       (P := fun c m => c!pc = Some i -> Ple r m).
   - intros. rewrite H in H1; auto.
   - rewrite PTree.gempty; congruence.
   - intros. rewrite PTree.gsspec in H3. destruct (peq pc k).
     + inv H3. eapply max_reg_instr_def; eauto.
     + apply Ple_trans with a. auto. apply max_reg_instr_ge.
  }
  unfold max_reg_function. xomega.
Qed.

Lemma max_reg_function_use:
  forall f pc i r,
  f.(fn_code)!pc = Some i -> In r (instr_uses i) -> Ple r (max_reg_function f).
Proof.
  intros.
  assert (Ple r (PTree.fold max_reg_instr f.(fn_code) 1%positive)).
  {  revert H.
     apply PTree_Properties.fold_rec with
       (P := fun c m => c!pc = Some i -> Ple r m).
   - intros. rewrite H in H1; auto.
   - rewrite PTree.gempty; congruence.
   - intros. rewrite PTree.gsspec in H3. destruct (peq pc k).
     + inv H3. eapply max_reg_instr_uses; eauto.
     + apply Ple_trans with a. auto. apply max_reg_instr_ge.
  }
  unfold max_reg_function. xomega.
Qed.

Lemma max_reg_function_params:
  forall f r, In r f.(fn_params) -> Ple r (max_reg_function f).
Proof.
  intros.
  assert (X: forall l n, In r l \/ Ple r n -> Ple r (fold_left Pmax l n)).
  { induction l; simpl; intros.
    tauto.
    apply IHl. destruct H0 as [[A|A]|A]. right; subst; xomega. auto. right; xomega. }
  assert (Y: Ple r (fold_left Pmax f.(fn_params) 1%positive)).
  { apply X; auto. }
  unfold max_reg_function. xomega.
Qed.

(** COMPCOMP NEW SECTION: Building an Effect semantics *)
Require Import sepcomp.effect_semantics.
Require Import sepcomp.mem_lemmas.

Section EFFSEM.

Variable ge: genv.

(** The transitions are presented as an inductive predicate
  [estep ge E st1 t st2], where [ge] is the global environment,
  [st1] the initial state, [st2] the final state, and [E] the write effects
  performed during this transition. *)

Inductive estep: (block -> Z -> bool) -> state -> mem -> state -> mem -> Prop :=
  | effexec_Inop:
      forall s f sp pc rs m pc',
      (fn_code f)!pc = Some(Inop pc') ->
      estep EmptyEffect (State s f sp pc rs) m
        (*E0*) (State s f sp pc' rs) m
  | effexec_Iop:
      forall s f sp pc rs m op args res pc' v,
      (fn_code f)!pc = Some(Iop op args res pc') ->
      eval_operation ge sp op rs##args m = Some v ->
      estep EmptyEffect (State s f sp pc rs) m
        (*E0*) (State s f sp pc' (rs#res <- v)) m
  | effexec_Iload:
      forall s f sp pc rs m chunk addr args dst pc' a v,
      (fn_code f)!pc = Some(Iload chunk addr args dst pc') ->
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.loadv chunk m a = Some v ->
      estep EmptyEffect (State s f sp pc rs) m
        (*E0*) (State s f sp pc' (rs#dst <- v)) m
  | effexec_Istore:
      forall s f sp pc rs m chunk addr args src pc' a m',
      (fn_code f)!pc = Some(Istore chunk addr args src pc') ->
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.storev chunk m a rs#src = Some m' ->
      estep (StoreEffect a (encode_val chunk (rs#src))) (State s f sp pc rs) m
        (*E0*) (State s f sp pc' rs) m'
  | effexec_Icall:
      forall s f sp pc rs m sig ros args res pc' fd,
      (fn_code f)!pc = Some(Icall sig ros args res pc') ->
      find_function ge ros rs = Some fd ->
      funsig fd = sig ->
      estep EmptyEffect (State s f sp pc rs) m
        (*E0*) (Callstate (Stackframe res f sp pc' rs :: s) fd rs##args) m
  | effexec_Itailcall:
      forall s f stk pc rs m sig ros args fd m',
      (fn_code f)!pc = Some(Itailcall sig ros args) ->
      find_function ge ros rs = Some fd ->
      funsig fd = sig ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      estep (FreeEffect m 0 (f.(fn_stacksize)) stk) (State s f (Vptr stk Int.zero) pc rs) m
        (*E0*) (Callstate s fd rs##args) m'
  | effexec_Ibuiltin:
      forall s f sp pc rs m ef args res pc' vargs t vres m',
      (fn_code f)!pc = Some(Ibuiltin ef args res pc') ->
      eval_builtin_args ge (fun r => rs#r) sp m args vargs ->
      external_call ef ge vargs m t vres m' ->
      (*COMPCOMP adaptation: limit to unobervables:*) ~ observableEF (*hf*) ef ->
      estep (BuiltinEffect ge ef vargs m) (State s f sp pc rs) m
         (*t*) (State s f sp pc' (regmap_setres res vres rs)) m'
  | effexec_Icond:
      forall s f sp pc rs m cond args ifso ifnot b pc',
      (fn_code f)!pc = Some(Icond cond args ifso ifnot) ->
      eval_condition cond rs##args m = Some b ->
      pc' = (if b then ifso else ifnot) ->
      estep EmptyEffect (State s f sp pc rs) m
        (*E0*) (State s f sp pc' rs) m
  | effexec_Ijumptable:
      forall s f sp pc rs m arg tbl n pc',
      (fn_code f)!pc = Some(Ijumptable arg tbl) ->
      rs#arg = Vint n ->
      list_nth_z tbl (Int.unsigned n) = Some pc' ->
      estep EmptyEffect (State s f sp pc rs) m
        (*E0*) (State s f sp pc' rs) m
  | effexec_Ireturn:
      forall s f stk pc rs m or m',
      (fn_code f)!pc = Some(Ireturn or) ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      estep (FreeEffect m 0 (f.(fn_stacksize)) stk) (State s f (Vptr stk Int.zero) pc rs) m
        (*E0*) (Returnstate s (regmap_optget or Vundef rs)) m'
  | effexec_function_internal:
      forall s f args m m' stk,
      Mem.alloc m 0 f.(fn_stacksize) = (m', stk) ->
      estep EmptyEffect (Callstate s (Internal f) args) m
        (*E0*) (State s
                  f
                  (Vptr stk Int.zero)
                  f.(fn_entrypoint)
                  (init_regs args f.(fn_params)))
                  m'
  | effexec_function_external:
      forall s ef args res t m m'
      (*COMPCOMP adaptation: restrict to helper functions*)(OBS: EFisHelper (*hf*) ef),
      external_call ef ge args m t res m' ->
      estep  (BuiltinEffect ge ef args m) (Callstate s (External ef) args) m
         (*t*) (Returnstate s res) m'
  | effexec_return:
      forall res f sp pc rs s vres m,
      estep EmptyEffect (Returnstate (Stackframe res f sp pc rs :: s) vres) m
        (*E0*) (State s f sp pc (rs#res <- vres)) m.

Lemma effexec_Iop':
  forall s f sp pc rs m op args res pc' rs' v,
  (fn_code f)!pc = Some(Iop op args res pc') ->
  eval_operation ge sp op rs##args m = Some v ->
  rs' = (rs#res <- v) ->
  estep EmptyEffect (State s f sp pc rs) m
    (*E0*) (State s f sp pc' rs') m.
Proof.
  intros. subst rs'. eapply effexec_Iop; eauto.
Qed.

Lemma effexec_Iload':
  forall s f sp pc rs m chunk addr args dst pc' rs' a v,
  (fn_code f)!pc = Some(Iload chunk addr args dst pc') ->
  eval_addressing ge sp addr rs##args = Some a ->
  Mem.loadv chunk m a = Some v ->
  rs' = (rs#dst <- v) ->
  estep EmptyEffect (State s f sp pc rs) m
    (*E0*) (State s f sp pc' rs') m.
Proof.
  intros. subst rs'. eapply effexec_Iload; eauto.
Qed.

Lemma rtl_effax1: forall (E : block -> Z -> bool) c m c' m',
      estep E c m c' m' ->
      (corestep (RTL_mem_sem (*hf*)) ge c m c' m' /\
       Mem.unchanged_on (fun b ofs => E b ofs = false) m m').
Proof. 
intros.
  induction H.
  split. eapply exec_Inop; eassumption.
         apply Mem.unchanged_on_refl.
  split. eapply exec_Iop; eassumption. 
         apply Mem.unchanged_on_refl.
  split. eapply exec_Iload; eassumption. 
         apply Mem.unchanged_on_refl.
  split. eapply exec_Istore; eassumption. 
         eapply StoreEffect_Storev; eassumption.
  split. eapply exec_Icall; eassumption. 
         apply Mem.unchanged_on_refl.
  split. eapply exec_Itailcall; eassumption. 
         eapply FreeEffect_free; eassumption. 
  split. econstructor; eassumption.
         eapply BuiltinEffect_unchOn; try eassumption.
(*  split. unfold corestep, coopsem; simpl. 
         eapply rtl_corestep_exec_Ibuiltin; eassumption.
         eapply ec_builtinEffectPolymorphic; eassumption.*)
  split. eapply exec_Icond; eassumption. 
         apply Mem.unchanged_on_refl.
  split. eapply exec_Ijumptable; eassumption. 
         apply Mem.unchanged_on_refl.
  split. eapply exec_Ireturn; eassumption. 
         eapply FreeEffect_free; eassumption. 
  split. eapply exec_function_internal; eassumption.
         eapply Mem.alloc_unchanged_on; eassumption. 
  split. eapply exec_function_external; eassumption.
         eapply BuiltinEffect_unchOn; try eassumption. 
         eapply EFhelpers; eassumption.
  split. eapply exec_return; eassumption.
         apply Mem.unchanged_on_refl.
Qed.

Lemma rtl_effax2: forall c m c' m',
      step ge c m c' m' ->
      exists E, estep E c m c' m'.
Proof.
intros. inv H.
    eexists. eapply effexec_Inop; eassumption.
    eexists. eapply effexec_Iop; eassumption.
    eexists. eapply effexec_Iload; eassumption.
    eexists. eapply effexec_Istore; eassumption.
    eexists. eapply effexec_Icall; try eassumption. trivial.
    eexists. eapply effexec_Itailcall; try eassumption. trivial.
    eexists. eapply effexec_Ibuiltin; eassumption.
    eexists. eapply effexec_Icond; try eassumption. trivial.
    eexists. eapply effexec_Ijumptable; eassumption.
    eexists. eapply effexec_Ireturn; eassumption.
    eexists. eapply effexec_function_internal; eassumption.
    eexists. eapply effexec_function_external; eassumption.
    eexists. eapply effexec_return.
Qed.

Lemma rtl_eff_perm: forall (E : block -> Z -> bool) c m c' m'
  (H: estep E c m c' m') b z (HE: E b z = true), Mem.perm m b z Cur Writable.
intros. inv H; try solve [unfold EmptyEffect in HE; simpl in HE; discriminate].
+ eapply storev_curWR; eassumption.
+ eapply free_curWR; eassumption.
+ eapply BuiltinEffect_CurWR; eassumption. 
+ eapply free_curWR; eassumption.
+ eapply BuiltinEffect_CurWR; eassumption. 
Qed. 

End EFFSEM.

Program Definition RTL_eff_sem : @EffectSem genv state.
Proof.
eapply Build_EffectSem with (sem := RTL_mem_sem (*hf*))(effstep:=estep).
intros. eapply rtl_effax1; eassumption.
apply rtl_effax2.
intros. eapply rtl_eff_perm; eassumption.
Defined.
