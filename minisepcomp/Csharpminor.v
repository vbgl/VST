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

(** Abstract syntax and semantics for the Csharpminor language. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import minisepcomp.Switch.
Require minisepcomp.Cminor_memsem.
Require Import Smallstep.

Require Import minisepcomp.BuiltinEffects.
Require Import sepcomp.semantics.
Require Import sepcomp.semantics_lemmas.
Require Import sepcomp.effect_semantics.

(** Abstract syntax *)

(** Csharpminor is a low-level imperative language structured in expressions,
  statements, functions and programs.  Expressions include
  reading temporary variables, taking the address of a variable,
  constants, arithmetic operations, and dereferencing addresses. *)

Inductive constant : Type :=
  | Ointconst: int -> constant          (**r integer constant *)
  | Ofloatconst: float -> constant      (**r double-precision floating-point constant *)
  | Osingleconst: float32 -> constant   (**r single-precision floating-point constant *)
  | Olongconst: int64 -> constant.      (**r long integer constant *)

Definition unary_operation : Type := Cminor_memsem.unary_operation.
Definition binary_operation : Type := Cminor_memsem.binary_operation.

Inductive expr : Type :=
  | Evar : ident -> expr                (**r reading a temporary variable  *)
  | Eaddrof : ident -> expr             (**r taking the address of a variable *)
  | Econst : constant -> expr           (**r constants *)
  | Eunop : unary_operation -> expr -> expr  (**r unary operation *)
  | Ebinop : binary_operation -> expr -> expr -> expr (**r binary operation *)
  | Eload : memory_chunk -> expr -> expr. (**r memory read *)

(** Statements include expression evaluation, temporary variable assignment,
  memory stores, function calls, an if/then/else conditional,
  infinite loops, blocks and early block exits, and early function returns.
  [Sexit n] terminates prematurely the execution of the [n+1] enclosing
  [Sblock] statements. *)

Definition label := ident.

Inductive stmt : Type :=
  | Sskip: stmt
  | Sset : ident -> expr -> stmt
  | Sstore : memory_chunk -> expr -> expr -> stmt
  | Scall : option ident -> signature -> expr -> list expr -> stmt
  | Sbuiltin : option ident -> external_function -> list expr -> stmt
  | Sseq: stmt -> stmt -> stmt
  | Sifthenelse: expr -> stmt -> stmt -> stmt
  | Sloop: stmt -> stmt
  | Sblock: stmt -> stmt
  | Sexit: nat -> stmt
  | Sswitch: bool -> expr -> lbl_stmt -> stmt
  | Sreturn: option expr -> stmt
  | Slabel: label -> stmt -> stmt
  | Sgoto: label -> stmt

with lbl_stmt : Type :=
  | LSnil: lbl_stmt
  | LScons: option Z -> stmt -> lbl_stmt -> lbl_stmt.

(** Functions are composed of a return type, a list of parameter names,
  a list of local variables with their sizes, a list of temporary variables,
  and a statement representing the function body.  *)

Record function : Type := mkfunction {
  fn_sig: signature;
  fn_params: list ident;
  fn_vars: list (ident * Z);
  fn_temps: list ident;
  fn_body: stmt
}.

Definition fundef := AST.fundef function.

Definition program : Type := AST.program fundef unit.

Definition funsig (fd: fundef) :=
  match fd with
  | Internal f => fn_sig f
  | External ef => ef_sig ef
  end.

(** * Operational semantics *)

(** Three evaluation environments are involved:
- [genv]: global environments, map symbols and functions to memory blocks,
    and maps symbols to variable informations (type [var_kind])
- [env]: local environments, map local variables
    to pairs (memory block, size)
- [temp_env]: local environments, map temporary variables to
    their current values.
*)

Definition genv := Genv.t fundef unit.
Definition env := PTree.t (block * Z).
Definition temp_env := PTree.t val.

Definition empty_env : env := PTree.empty (block * Z).
Definition empty_temp_env : temp_env := PTree.empty val.

(** Initialization of temporary variables *)

Fixpoint create_undef_temps (temps: list ident) : temp_env :=
  match temps with
  | nil => PTree.empty val
  | id :: temps' => PTree.set id Vundef (create_undef_temps temps')
 end.

(** Initialization of temporaries that are parameters. *)

Fixpoint bind_parameters (formals: list ident) (args: list val)
                         (le: temp_env) : option temp_env :=
 match formals, args with
 | nil, nil => Some le
 | id :: xl, v :: vl => bind_parameters xl vl (PTree.set id v le)
 | _, _ => None
 end.

(** Continuations *)

Inductive cont: Type :=
  | Kstop: cont                         (**r stop program execution *)
  | Kseq: stmt -> cont -> cont          (**r execute stmt, then cont *)
  | Kblock: cont -> cont                (**r exit a block, then do cont *)
  | Kcall: option ident -> function -> env -> temp_env -> cont -> cont.
                                        (**r return to caller *)

(** States *)

(*CompComp adaptation: removed mem in all constructors*)
Inductive state: Type :=
  | State:                      (**r Execution within a function *)
      forall (f: function)              (**r currently executing function  *)
             (s: stmt)                  (**r statement under consideration *)
             (k: cont)                  (**r its continuation -- what to do next *)
             (e: env)                   (**r current local environment *)
             (le: temp_env),            (**r current temporary environment *)
      state
  | Callstate:                  (**r Invocation of a function *)
      forall (f: fundef)                (**r function to invoke *)
             (args: list val)           (**r arguments provided by caller *)
             (k: cont),                 (**r what to do next  *)
      state
  | Returnstate:                (**r Return from a function *)
      forall (v: val)                   (**r Return value *)
             (k: cont),                 (**r what to do next *)
      state.

(** Pop continuation until a call or stop *)

Fixpoint call_cont (k: cont) : cont :=
  match k with
  | Kseq s k => call_cont k
  | Kblock k => call_cont k
  | _ => k
  end.

Definition is_call_cont (k: cont) : Prop :=
  match k with
  | Kstop => True
  | Kcall _ _ _ _ _ => True
  | _ => False
  end.

(** Resolve [switch] statements. *)

Fixpoint select_switch_default (sl: lbl_stmt): lbl_stmt :=
  match sl with
  | LSnil => sl
  | LScons None s sl' => sl
  | LScons (Some i) s sl' => select_switch_default sl'
  end.

Fixpoint select_switch_case (n: Z) (sl: lbl_stmt): option lbl_stmt :=
  match sl with
  | LSnil => None
  | LScons None s sl' => select_switch_case n sl'
  | LScons (Some c) s sl' => if zeq c n then Some sl else select_switch_case n sl'
  end.

Definition select_switch (n: Z) (sl: lbl_stmt): lbl_stmt :=
  match select_switch_case n sl with
  | Some sl' => sl'
  | None => select_switch_default sl
  end.

Fixpoint seq_of_lbl_stmt (sl: lbl_stmt) : stmt :=
  match sl with
  | LSnil => Sskip
  | LScons c s sl' => Sseq s (seq_of_lbl_stmt sl')
  end.

(** Find the statement and manufacture the continuation
  corresponding to a label *)

Fixpoint find_label (lbl: label) (s: stmt) (k: cont)
                    {struct s}: option (stmt * cont) :=
  match s with
  | Sseq s1 s2 =>
      match find_label lbl s1 (Kseq s2 k) with
      | Some sk => Some sk
      | None => find_label lbl s2 k
      end
  | Sifthenelse a s1 s2 =>
      match find_label lbl s1 k with
      | Some sk => Some sk
      | None => find_label lbl s2 k
      end
  | Sloop s1 =>
      find_label lbl s1 (Kseq (Sloop s1) k)
  | Sblock s1 =>
      find_label lbl s1 (Kblock k)
  | Sswitch long a sl =>
      find_label_ls lbl sl k
  | Slabel lbl' s' =>
      if ident_eq lbl lbl' then Some(s', k) else find_label lbl s' k
  | _ => None
  end

with find_label_ls (lbl: label) (sl: lbl_stmt) (k: cont)
                   {struct sl}: option (stmt * cont) :=
  match sl with
  | LSnil => None
  | LScons _ s sl' =>
      match find_label lbl s (Kseq (seq_of_lbl_stmt sl') k) with
      | Some sk => Some sk
      | None => find_label_ls lbl sl' k
      end
  end.

(** Evaluation of operator applications. *)

Definition eval_constant (cst: constant) : option val :=
  match cst with
  | Ointconst n => Some (Vint n)
  | Ofloatconst n => Some (Vfloat n)
  | Osingleconst n => Some (Vsingle n)
  | Olongconst n => Some (Vlong n)
  end.

Definition eval_unop := Cminor_memsem.eval_unop.

Definition eval_binop := Cminor_memsem.eval_binop.

(** Allocation of local variables at function entry.  Each variable is
  bound to the reference to a fresh block of the appropriate size. *)

Inductive alloc_variables: env -> mem ->
                           list (ident * Z) ->
                           env -> mem -> Prop :=
  | alloc_variables_nil:
      forall e m,
      alloc_variables e m nil e m
  | alloc_variables_cons:
      forall e m id sz vars m1 b1 m2 e2,
      Mem.alloc m 0 sz = (m1, b1) ->
      alloc_variables (PTree.set id (b1, sz) e) m1 vars e2 m2 ->
      alloc_variables e m ((id, sz) :: vars) e2 m2.

(** List of blocks mentioned in an environment, with low and high bounds *)

Definition block_of_binding (id_b_sz: ident * (block * Z)) :=
  match id_b_sz with (id, (b, sz)) => (b, 0, sz) end.

Definition blocks_of_env (e: env) : list (block * Z * Z) :=
  List.map block_of_binding (PTree.elements e).

Section RELSEM.

Variable ge: genv.

(* Evaluation of the address of a variable:
   [eval_var_addr prg ge e id b] states that variable [id]
   in environment [e] evaluates to block [b]. *)

Inductive eval_var_addr: env -> ident -> block -> Prop :=
  | eval_var_addr_local:
      forall e id b sz,
      PTree.get id e = Some (b, sz) ->
      eval_var_addr e id b
  | eval_var_addr_global:
      forall e id b,
      PTree.get id e = None ->
      Genv.find_symbol ge id = Some b ->
      eval_var_addr e id b.

(** Evaluation of an expression: [eval_expr prg e m a v] states
  that expression [a], in initial memory state [m] and local
  environment [e], evaluates to value [v]. *)

Section EVAL_EXPR.

Variable e: env.
Variable le: temp_env.
Variable m: mem.

Inductive eval_expr: expr -> val -> Prop :=
  | eval_Evar: forall id v,
      le!id = Some v ->
      eval_expr (Evar id) v
  | eval_Eaddrof: forall id b,
      eval_var_addr e id b ->
      eval_expr (Eaddrof id) (Vptr b Int.zero)
  | eval_Econst: forall cst v,
      eval_constant cst = Some v ->
      eval_expr (Econst cst) v
  | eval_Eunop: forall op a1 v1 v,
      eval_expr a1 v1 ->
      eval_unop op v1 = Some v ->
      eval_expr (Eunop op a1) v
  | eval_Ebinop: forall op a1 a2 v1 v2 v,
      eval_expr a1 v1 ->
      eval_expr a2 v2 ->
      eval_binop op v1 v2 m = Some v ->
      eval_expr (Ebinop op a1 a2) v
  | eval_Eload: forall chunk a v1 v,
      eval_expr a v1 ->
      Mem.loadv chunk m v1 = Some v ->
      eval_expr (Eload chunk a) v.

(** Evaluation of a list of expressions:
  [eval_exprlist prg e m al vl] states that the list [al] of
  expressions evaluate to the list [vl] of values.  The other
  parameters are as in [eval_expr]. *)

Inductive eval_exprlist: list expr -> list val -> Prop :=
  | eval_Enil:
      eval_exprlist nil nil
  | eval_Econs: forall a1 al v1 vl,
      eval_expr a1 v1 -> eval_exprlist al vl ->
      eval_exprlist (a1 :: al) (v1 :: vl).

End EVAL_EXPR.

(** One step of execution *)

(*CompComp adaptation: refactored states, removed traces, added obs*)
Inductive step: state -> mem -> state -> mem -> Prop :=

  | step_skip_seq: forall f s k e le m,
      step (State f Sskip (Kseq s k) e le) m
        (State f s k e le) m
  | step_skip_block: forall f k e le m,
      step (State f Sskip (Kblock k) e le) m
        (State f Sskip k e le) m
  | step_skip_call: forall f k e le m m',
      is_call_cont k ->
      Mem.free_list m (blocks_of_env e) = Some m' ->
      step (State f Sskip k e le) m
        (Returnstate Vundef k) m'

  | step_set: forall f id a k e le m v,
      eval_expr e le m a v ->
      step (State f (Sset id a) k e le) m
        (State f Sskip k e (PTree.set id v le)) m

  | step_store: forall f chunk addr a k e le m vaddr v m',
      eval_expr e le m addr vaddr ->
      eval_expr e le m a v ->
      Mem.storev chunk m vaddr v = Some m' ->
      step (State f (Sstore chunk addr a) k e le) m
        (State f Sskip k e le) m'

  | step_call: forall f optid sig a bl k e le m vf vargs fd,
      eval_expr e le m a vf ->
      eval_exprlist e le m bl vargs ->
      Genv.find_funct ge vf = Some fd ->
      funsig fd = sig ->
      step (State f (Scall optid sig a bl) k e le) m
        (Callstate fd vargs (Kcall optid f e le k)) m

  | step_builtin: forall f optid ef bl k e le m vargs t vres m'
      (*COMPCOMP adaptation: limit to unobervables:*) (NOBS:~ observableEF (*hf*) ef),
      eval_exprlist e le m bl vargs ->
      external_call ef ge vargs m t vres m' ->
      step (State f (Sbuiltin optid ef bl) k e le) m
        (State f Sskip k e (Cminor_memsem.set_optvar optid vres le)) m'

  | step_seq: forall f s1 s2 k e le m,
      step (State f (Sseq s1 s2) k e le) m
        (State f s1 (Kseq s2 k) e le) m

  | step_ifthenelse: forall f a s1 s2 k e le m v b,
      eval_expr e le m a v ->
      Val.bool_of_val v b ->
      step (State f (Sifthenelse a s1 s2) k e le) m
        (State f (if b then s1 else s2) k e le) m

  | step_loop: forall f s k e le m,
      step (State f (Sloop s) k e le) m
        (State f s (Kseq (Sloop s) k) e le) m

  | step_block: forall f s k e le m,
      step (State f (Sblock s) k e le) m
        (State f s (Kblock k) e le) m

  | step_exit_seq: forall f n s k e le m,
      step (State f (Sexit n) (Kseq s k) e le) m
        (State f (Sexit n) k e le) m
  | step_exit_block_0: forall f k e le m,
      step (State f (Sexit O) (Kblock k) e le) m
        (State f Sskip k e le) m
  | step_exit_block_S: forall f n k e le m,
      step (State f (Sexit (S n)) (Kblock k) e le) m
        (State f (Sexit n) k e le) m

  | step_switch: forall f islong a cases k e le m v n,
      eval_expr e le m a v ->
      switch_argument islong v n ->
      step (State f (Sswitch islong a cases) k e le) m
        (State f (seq_of_lbl_stmt (select_switch n cases)) k e le) m

  | step_return_0: forall f k e le m m',
      Mem.free_list m (blocks_of_env e) = Some m' ->
      step (State f (Sreturn None) k e le) m
        (Returnstate Vundef (call_cont k)) m'
  | step_return_1: forall f a k e le m v m',
      eval_expr e le m a v ->
      Mem.free_list m (blocks_of_env e) = Some m' ->
      step (State f (Sreturn (Some a)) k e le) m
        (Returnstate v (call_cont k)) m'
  | step_label: forall f lbl s k e le m,
      step (State f (Slabel lbl s) k e le) m
        (State f s k e le) m

  | step_goto: forall f lbl k e le m s' k',
      find_label lbl f.(fn_body) (call_cont k) = Some(s', k') ->
      step (State f (Sgoto lbl) k e le) m
        (State f s' k' e le) m

  | step_internal_function: forall f vargs k m m1 e le,
      list_norepet (map fst f.(fn_vars)) ->
      list_norepet f.(fn_params) ->
      list_disjoint f.(fn_params) f.(fn_temps) ->
      alloc_variables empty_env m (fn_vars f) e m1 ->
      bind_parameters f.(fn_params) vargs (create_undef_temps f.(fn_temps)) = Some le ->
      step (Callstate (Internal f) vargs k) m
        (State f f.(fn_body) k e le) m1

  | step_external_function: forall ef vargs k m t vres m'
      (*COMPCOMP adaptation: restrict to helper functions*)(OBS: EFisHelper (*hf*) ef),
      external_call ef ge vargs m t vres m' ->
      step (Callstate (External ef) vargs k) m
         (Returnstate vres k) m'

  | step_return: forall v optid f e le k m,
      step (Returnstate v (Kcall optid f e le k)) m
        (State f Sskip k e (Cminor_memsem.set_optvar optid v le)) m.

End RELSEM.

(** Execution of whole programs are described as sequences of transitions
  from an initial state to a final state.  An initial state is a [Callstate]
  corresponding to the invocation of the ``main'' function of the program
  without arguments and with an empty continuation. *)
(*
Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall b f m0,
      let ge := Genv.globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      funsig f = signature_main ->
      initial_state p (Callstate f nil Kstop m0).
*)
Definition CSharpMin_initial_core (ge:genv) (v: val) (args:list val): option state :=
   match v with
     | Vptr b i => 
          if Int.eq_dec i Int.zero 
          then match Genv.find_funct_ptr ge b with
                 | None => None
                 | Some f => 
                    match f with Internal fi =>
                      if (*CompComp: TODO: reactivate later val_has_type_list_func args (sig_args (funsig f))
                         && vals_defined args
                         &&*) zlt (4*(2*(Zlength args))) Int.max_unsigned
                      then Some (Callstate f args Kstop)
                      else None
                    | External _ => None
                    end 
               end
          else None
     | _ => None
    end.

(** A final state is a [Returnstate] with an empty continuation. *)
(*
Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall r m,
      final_state (Returnstate (Vint r) Kstop m) r.
*)
Definition CSharpMin_halted (q : state): option val :=
    match q with 
       Returnstate v Kstop => Some v
     | _ => None
    end.

Definition CSharpMin_at_external (c: state) : option (external_function * signature * list val) :=
  match c with
  | State _ _ _ _ _ => None
  | Callstate fd args k =>
        match fd with
          Internal f => None
         | External ef => if observableEF_dec (*hf*) ef 
                          then Some (ef, ef_sig ef, args)
                          else None
        end
  | Returnstate v k => None
 end.

Definition CSharpMin_after_external (vret: option val) (c: state) : option state :=
  match c with 
    Callstate fd args k => 
         match fd with
            Internal f => None
          | External ef => match vret with
                             None => Some (Returnstate Vundef k)
                           | Some v => Some (Returnstate v k)
                           end
         end
  | _ => None
  end.

(** Wrapping up these definitions in a small-step semantics. *)
(*
Definition semantics (p: program) :=
  Semantics step (initial_state p) final_state (Genv.globalenv p).*)
Lemma CSharpMin_corestep_not_at_external:
       forall ge m q m' q', step ge q m q' m' -> 
       CSharpMin_at_external q = None.
  Proof. intros. inv H; try reflexivity. 
  simpl. destruct (observableEF_dec (*hf*) ef); simpl; trivial. 
  eelim EFhelpers; eassumption. Qed. 

Lemma CSharpMin_corestep_not_halted : forall ge m q m' q', 
        step ge q m q' m' -> CSharpMin_halted q = None.
  Proof. intros. inv H; reflexivity. Qed.
    
Lemma CSharpMin_at_external_halted_excl :
       forall q, CSharpMin_at_external q = None \/ CSharpMin_halted q = None.
   Proof. intros. destruct q; auto. Qed.

Lemma CSharpMin_after_at_external_excl : forall retv q q',
      CSharpMin_after_external retv q = Some q' -> CSharpMin_at_external q' = None.
  Proof. intros.
       destruct q; simpl in *; try inv H.
       destruct f; try inv H1; simpl; trivial.
         destruct retv; inv H0; simpl; trivial.
Qed.

Definition CSharpMin_core_sem : CoreSemantics genv state mem.
Proof.
  eapply (@Build_CoreSemantics _ _ _ 
    CSharpMin_initial_core
    CSharpMin_at_external
    CSharpMin_after_external
    CSharpMin_halted
    step).
  apply CSharpMin_corestep_not_at_external.
  apply CSharpMin_corestep_not_halted.
  apply CSharpMin_at_external_halted_excl.
Defined.

Lemma alloc_variables_mem_step: forall vars m e e2 m'
      (M: alloc_variables e m vars e2 m'),
      mem_step m m'.
Proof. intros.
  induction M.
  apply mem_step_refl.
  apply mem_step_alloc in H.
  eapply mem_step_trans; eassumption. 
Qed.

Lemma cshmin_step_mem : forall g c m c' m' (CS: step g c m c' m'), mem_step m m'.
Proof. intros.
       inv CS; try apply mem_step_refl.
       + eapply mem_step_freelist; eassumption.
       + destruct vaddr; simpl in H1; inv H1. 
         eapply mem_step_store; eassumption.
       + admit. (*external call to unobservable function -- needs axiom
         eapply external_call_mem_step; eassumption.*)
       + eapply mem_step_freelist; eassumption.
       + eapply mem_step_freelist; eassumption.
       + eapply alloc_variables_mem_step; eauto.
       + admit. (*external call to helper function -- needs axiom
         eapply external_call_mem_step; eassumption.*)
Admitted.

Program Definition CSharpMin_memsem : MemSem genv state.
Proof.
apply Build_MemSem with (csem := CSharpMin_core_sem).
  apply cshmin_step_mem.
Defined.

(** COMPCOMP NEW SECTION: Building an Effect semantics *)

Section EFFSEM_STEP.

Variable ge: genv.

Inductive estep: (block -> Z -> bool) -> state -> mem -> state -> mem -> Prop :=

  | estep_skip_seq: forall f s k e le m,
      estep EmptyEffect (State f Sskip (Kseq s k) e le) m
        (State f s k e le) m
  | estep_skip_block: forall f k e le m,
      estep EmptyEffect (State f Sskip (Kblock k) e le) m
        (State f Sskip k e le) m
  | estep_skip_call: forall f k e le m m',
      is_call_cont k ->
      Mem.free_list m (blocks_of_env e) = Some m' ->
      estep (FreelistEffect m (blocks_of_env e))
            (State f Sskip k e le) m
            (Returnstate Vundef k) m'

  | estep_set: forall f id a k e le m v,
      eval_expr ge e le m a v ->
      estep EmptyEffect (State f (Sset id a) k e le) m
        (State f Sskip k e (PTree.set id v le)) m

  | estep_store: forall f chunk addr a k e le m vaddr v m',
      eval_expr ge e le m addr vaddr ->
      eval_expr ge e le m a v ->
      Mem.storev chunk m vaddr v = Some m' ->
      estep (StoreEffect vaddr (encode_val chunk v))
            (State f (Sstore chunk addr a) k e le) m
            (State f Sskip k e le) m'

  | estep_call: forall f optid sig a bl k e le m vf vargs fd,
      eval_expr ge e le m a vf ->
      eval_exprlist ge e le m bl vargs ->
      Genv.find_funct ge vf = Some fd ->
      funsig fd = sig ->
      estep EmptyEffect (State f (Scall optid sig a bl) k e le) m
        (Callstate fd vargs (Kcall optid f e le k)) m

  | estep_builtin: forall f optid ef bl k e le m vargs t vres m'
      (*COMPCOMP adaptation: limit to unobervables:*) (NOBS:~ observableEF (*hf*) ef),
      eval_exprlist ge e le m bl vargs ->
      external_call ef ge vargs m t vres m' ->
      estep (BuiltinEffect ge ef vargs m)
            (State f (Sbuiltin optid ef bl) k e le) m
            (State f Sskip k e (Cminor_memsem.set_optvar optid vres le)) m'

  | estep_seq: forall f s1 s2 k e le m,
      estep EmptyEffect
            (State f (Sseq s1 s2) k e le) m
            (State f s1 (Kseq s2 k) e le) m

  | estep_ifthenelse: forall f a s1 s2 k e le m v b,
      eval_expr ge e le m a v ->
      Val.bool_of_val v b ->
      estep EmptyEffect (State f (Sifthenelse a s1 s2) k e le) m
        (State f (if b then s1 else s2) k e le) m

  | estep_loop: forall f s k e le m,
      estep EmptyEffect (State f (Sloop s) k e le) m
        (State f s (Kseq (Sloop s) k) e le) m

  | estep_block: forall f s k e le m,
      estep EmptyEffect (State f (Sblock s) k e le) m
        (State f s (Kblock k) e le) m

  | estep_exit_seq: forall f n s k e le m,
      estep EmptyEffect (State f (Sexit n) (Kseq s k) e le) m
        (State f (Sexit n) k e le) m
  | estep_exit_block_0: forall f k e le m,
      estep EmptyEffect (State f (Sexit O) (Kblock k) e le) m
        (State f Sskip k e le) m
  | estep_exit_block_S: forall f n k e le m,
      estep EmptyEffect (State f (Sexit (S n)) (Kblock k) e le) m
        (State f (Sexit n) k e le) m

  | estep_switch: forall f islong a cases k e le m v n,
      eval_expr ge e le m a v ->
      switch_argument islong v n ->
      estep EmptyEffect (State f (Sswitch islong a cases) k e le) m
        (State f (seq_of_lbl_stmt (select_switch n cases)) k e le) m

  | estep_return_0: forall f k e le m m',
      Mem.free_list m (blocks_of_env e) = Some m' ->
      estep (FreelistEffect m (blocks_of_env e))
            (State f (Sreturn None) k e le) m
            (Returnstate Vundef (call_cont k)) m'
  | estep_return_1: forall f a k e le m v m',
      eval_expr ge e le m a v ->
      Mem.free_list m (blocks_of_env e) = Some m' ->
      estep (FreelistEffect m (blocks_of_env e))
            (State f (Sreturn (Some a)) k e le) m
            (Returnstate v (call_cont k)) m'
  | estep_label: forall f lbl s k e le m,
      estep EmptyEffect (State f (Slabel lbl s) k e le) m
        (State f s k e le) m

  | estep_goto: forall f lbl k e le m s' k',
      find_label lbl f.(fn_body) (call_cont k) = Some(s', k') ->
      estep EmptyEffect (State f (Sgoto lbl) k e le) m
        (State f s' k' e le) m

  | estep_internal_function: forall f vargs k m m1 e le,
      list_norepet (map fst f.(fn_vars)) ->
      list_norepet f.(fn_params) ->
      list_disjoint f.(fn_params) f.(fn_temps) ->
      alloc_variables empty_env m (fn_vars f) e m1 ->
      bind_parameters f.(fn_params) vargs (create_undef_temps f.(fn_temps)) = Some le ->
      estep EmptyEffect (Callstate (Internal f) vargs k) m
        (State f f.(fn_body) k e le) m1

  | estep_external_function: forall ef vargs k m t vres m'
      (*COMPCOMP adaptation: restrict to helper functions*)(OBS: EFisHelper (*hf*) ef),
      external_call ef ge vargs m t vres m' ->
      estep (BuiltinEffect ge ef vargs m) (Callstate (External ef) vargs k) m
         (Returnstate vres k) m'

  | estep_return: forall v optid f e le k m,
      estep EmptyEffect (Returnstate v (Kcall optid f e le k)) m
        (State f Sskip k e (Cminor_memsem.set_optvar optid v le)) m.

End EFFSEM_STEP.

Section CSHARPMINOR_EFF.

Lemma EmptyEffect_allocvariables: forall L e m e' m'
      (ALLOC: alloc_variables e m L e' m'),
  Mem.unchanged_on (fun b ofs => EmptyEffect b ofs = false) m m'.
Proof. intros L.
  induction L; simpl; intros; inv ALLOC.
    apply Mem.unchanged_on_refl.
  specialize (IHL _ _ _ _ H6). clear H6.
  eapply Mem.unchanged_on_trans; eauto.
    eapply EmptyEffect_alloc; eassumption.
Qed.

Lemma csharpminstep_effax1: forall (M : block -> Z -> bool) g c m c' m'
      (H: estep g M c m c' m'),
       step (*hf*) g c m c' m' /\
       Mem.unchanged_on (fun (b : block) (ofs : Z) => M b ofs = false) m m'.
Proof. 
intros.
  induction H; try solve [split; [ econstructor; eauto | try apply Mem.unchanged_on_refl] ].
  split; [ econstructor; eauto |]. eapply FreelistEffect_freelist; eassumption. 
  split; [ econstructor; eauto |]. eapply StoreEffect_Storev; eassumption.
  split; [ econstructor; eauto |]. eapply BuiltinEffect_unchOn; eassumption.
  split; [ econstructor; eauto |]. eapply FreelistEffect_freelist; eassumption.
  split; [ econstructor; eauto |]. eapply FreelistEffect_freelist; eassumption.
  split; [ econstructor; eauto |]. eapply EmptyEffect_allocvariables; eassumption.
  split; [ econstructor; eauto |]. apply EFhelpers in OBS. eapply BuiltinEffect_unchOn; eassumption.
Qed.

Lemma csharpminstep_effax2: forall  g c m c' m',
      step(*hf*) g c m c' m' ->
      exists M, estep g M c m c' m'.
Proof.
intros. inv H; solve [eexists; econstructor; eauto]. Qed.

Lemma csharpmin_eff_perm: forall (E : block -> Z -> bool) ge c m c' m'
  (H: estep ge E c m c' m') b z (HE: E b z = true), Mem.perm m b z Cur Writable.
intros. inv H; try solve [unfold EmptyEffect in HE; simpl in HE; discriminate].
+ eapply freelist_curWR; eassumption.
+ eapply storev_curWR; eassumption.
+ eapply BuiltinEffect_CurWR; eassumption. 
+ eapply freelist_curWR; eassumption.
+ eapply freelist_curWR; eassumption.
+ eapply BuiltinEffect_CurWR; eassumption. 
Qed. 

Program Definition csharpmin_eff_sem : 
  @EffectSem genv state.
Proof.
eapply Build_EffectSem with (sem := CSharpMin_memsem (*hf*))
       (effstep:=estep).
apply csharpminstep_effax1.
apply csharpminstep_effax2. 
apply csharpmin_eff_perm. 
Defined.

End CSHARPMINOR_EFF.



