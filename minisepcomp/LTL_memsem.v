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

(** The LTL intermediate language: abstract syntax and semantics.

  LTL (``Location Transfer Language'') is the target language
  for register allocation and the source language for linearization. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Events.
Require Import Memory.
Require Import Globalenvs.
Require Import Smallstep.
Require Import minisepcomp.Op.
Require Import minisepcomp.Locations.
Require Import minisepcomp.Conventions.
Require Import minisepcomp.BuiltinEffects.

Require Import minisepcomp.val_casted.

(** * Abstract syntax *)

(** LTL is close to RTL, but uses machine registers and stack slots
  instead of pseudo-registers.  Also, the nodes of the control-flow
  graph are basic blocks instead of single instructions. *)

Definition node := positive.

Inductive instruction: Type :=
  | Lop (op: operation) (args: list mreg) (res: mreg)
  | Lload (chunk: memory_chunk) (addr: addressing) (args: list mreg) (dst: mreg)
  | Lgetstack (sl: slot) (ofs: Z) (ty: typ) (dst: mreg)
  | Lsetstack (src: mreg) (sl: slot) (ofs: Z) (ty: typ)
  | Lstore (chunk: memory_chunk) (addr: addressing) (args: list mreg) (src: mreg)
  | Lcall (sg: signature) (ros: mreg + ident)
  | Ltailcall (sg: signature) (ros: mreg + ident)
  | Lbuiltin (ef: external_function) (args: list (builtin_arg loc)) (res: builtin_res mreg)
  | Lbranch (s: node)
  | Lcond (cond: condition) (args: list mreg) (s1 s2: node)
  | Ljumptable (arg: mreg) (tbl: list node)
  | Lreturn.

Definition bblock := list instruction.

Definition code: Type := PTree.t bblock.

Record function: Type := mkfunction {
  fn_sig: signature;
  fn_stacksize: Z;
  fn_code: code;
  fn_entrypoint: node
}.

Definition fundef := AST.fundef function.

Definition program := AST.program fundef unit.

Definition funsig (fd: fundef) :=
  match fd with
  | Internal f => fn_sig f
  | External ef => ef_sig ef
  end.

(** * Operational semantics *)

Definition genv := Genv.t fundef unit.
Definition locset := Locmap.t.

(** Calling conventions are reflected at the level of location sets
  (environments mapping locations to values) by the following two
  functions.

  [call_regs caller] returns the location set at function entry,
  as a function of the location set [caller] of the calling function.
- Machine registers have the same values as in the caller.
- Incoming stack slots (used for parameter passing) have the same
  values as the corresponding outgoing stack slots (used for argument
  passing) in the caller.
- Local and outgoing stack slots are initialized to undefined values.
*)

Definition call_regs (caller: locset) : locset :=
  fun (l: loc) =>
    match l with
    | R r => caller (R r)
    | S Local ofs ty => Vundef
    | S Incoming ofs ty => caller (S Outgoing ofs ty)
    | S Outgoing ofs ty => Vundef
    end.

(** [return_regs caller callee] returns the location set after
  a call instruction, as a function of the location set [caller]
  of the caller before the call instruction and of the location
  set [callee] of the callee at the return instruction.
- Callee-save machine registers have the same values as in the caller
  before the call.
- Caller-save machine registers have the same values as in the callee.
- Stack slots have the same values as in the caller.
*)

Definition return_regs (caller callee: locset) : locset :=
  fun (l: loc) =>
    match l with
    | R r => if is_callee_save r then caller (R r) else callee (R r)
    | S sl ofs ty => caller (S sl ofs ty)
    end.

(** LTL execution states. *)

Inductive stackframe : Type :=
  | Stackframe:
      forall (f: function)      (**r calling function *)
             (sp: val)          (**r stack pointer in calling function *)
             (ls: locset)       (**r location state in calling function *)
             (bb: bblock),      (**r continuation in calling function *)
      stackframe.

(*COMPCOMP adaptation: removed mem components in all 4 constructors, and introduced retty*)
Inductive state : Type :=
  | State:
      forall (stack: list stackframe) (**r call stack *)
             (f: function)            (**r function currently executing *)
             (sp: val)                (**r stack pointer *)
             (pc: node)               (**r current program point *)
             (ls: locset)             (**r location state *)
             (retty: option typ),     (**r return type at halted *)
      state
  | Block:
      forall (stack: list stackframe) (**r call stack *)
             (f: function)            (**r function currently executing *)
             (sp: val)                (**r stack pointer *)
             (bb: bblock)             (**r current basic block *)
             (ls: locset)             (**r location state *)
             (retty: option typ),     (**r return type at halted *)
      state
  | Callstate:
      forall (stack: list stackframe) (**r call stack *)
             (f: fundef)              (**r function to call *)
             (ls: locset)             (**r location state of caller *)
             (retty: option typ),     (**r return type at halted *)
      state
  | Returnstate:
      forall (stack: list stackframe) (**r call stack *)
             (ls: locset)             (**r location state of callee *)
             (retty: option typ),     (**r return type at halted *)
      state.


Section RELSEM.

Variable ge: genv.

Definition reglist (rs: locset) (rl: list mreg) : list val :=
  List.map (fun r => rs (R r)) rl.

Fixpoint undef_regs (rl: list mreg) (rs: locset) : locset :=
  match rl with
  | nil => rs
  | r1 :: rl => Locmap.set (R r1) Vundef (undef_regs rl rs)
  end.

Definition destroyed_by_getstack (s: slot): list mreg :=
  match s with
  | Incoming => temp_for_parent_frame :: nil
  | _        => nil
  end.

Definition find_function (ros: mreg + ident) (rs: locset) : option fundef :=
  match ros with
  | inl r => Genv.find_funct ge (rs (R r))
  | inr symb =>
      match Genv.find_symbol ge symb with
      | None => None
      | Some b => Genv.find_funct_ptr ge b
      end
  end.

(** [parent_locset cs] returns the mapping of values for locations
  of the caller function. *)

Definition parent_locset (stack: list stackframe) : locset :=
  match stack with
  | nil => Locmap.init Vundef
  | Stackframe f sp ls bb :: stack' => ls
  end.

(*CopComp adaptation: old type:state -> trace -> state -> Prop*)
Inductive step: state -> mem -> state -> mem -> Prop :=
  | exec_start_block: forall s f sp pc rs m bb rty,
      (fn_code f)!pc = Some bb ->
      step (State s f sp pc rs rty) m
        (*E0*) (Block s f sp bb rs rty) m
  | exec_Lop: forall s f sp op args res bb rs m v rs' rty,
      eval_operation ge sp op (reglist rs args) m = Some v ->
      rs' = Locmap.set (R res) v (undef_regs (destroyed_by_op op) rs) ->
      step (Block s f sp (Lop op args res :: bb) rs rty) m
        (*E0*) (Block s f sp bb rs' rty) m
  | exec_Lload: forall s f sp chunk addr args dst bb rs m a v rs' rty,
      eval_addressing ge sp addr (reglist rs args) = Some a ->
      Mem.loadv chunk m a = Some v ->
      rs' = Locmap.set (R dst) v (undef_regs (destroyed_by_load chunk addr) rs) ->
      step (Block s f sp (Lload chunk addr args dst :: bb) rs rty) m
        (*E0*) (Block s f sp bb rs' rty) m
  | exec_Lgetstack: forall s f sp sl ofs ty dst bb rs m rs' rty,
      rs' = Locmap.set (R dst) (rs (S sl ofs ty)) (undef_regs (destroyed_by_getstack sl) rs) ->
      step (Block s f sp (Lgetstack sl ofs ty dst :: bb) rs rty) m
        (*E0*) (Block s f sp bb rs' rty) m
  | exec_Lsetstack: forall s f sp src sl ofs ty bb rs m rs' rty,
      rs' = Locmap.set (S sl ofs ty) (rs (R src)) (undef_regs (destroyed_by_setstack ty) rs) ->
      step (Block s f sp (Lsetstack src sl ofs ty :: bb) rs rty) m
        (*E0*) (Block s f sp bb rs' rty) m
  | exec_Lstore: forall s f sp chunk addr args src bb rs m a rs' m' rty,
      eval_addressing ge sp addr (reglist rs args) = Some a ->
      Mem.storev chunk m a (rs (R src)) = Some m' ->
      rs' = undef_regs (destroyed_by_store chunk addr) rs ->
      step (Block s f sp (Lstore chunk addr args src :: bb) rs rty) m
        (*E0*) (Block s f sp bb rs' rty) m'
  | exec_Lcall: forall s f sp sig ros bb rs m fd rty,
      find_function ros rs = Some fd ->
      funsig fd = sig ->
      step (Block s f sp (Lcall sig ros :: bb) rs rty) m
        (*E0*) (Callstate (Stackframe f sp rs bb :: s) fd rs rty) m
  | exec_Ltailcall: forall s f sp sig ros bb rs m fd rs' m' rty,
      rs' = return_regs (parent_locset s) rs ->
      find_function ros rs' = Some fd ->
      funsig fd = sig ->
      Mem.free m sp 0 f.(fn_stacksize) = Some m' ->
      step (Block s f (Vptr sp Int.zero) (Ltailcall sig ros :: bb) rs rty) m
        (*E0*) (Callstate s fd rs' rty) m'
  | exec_Lbuiltin: forall s f sp ef args res bb rs m vargs t vres rs' m' rty
      (*COMPCOMP adaptation: limit to unobervables:*) (NOBS: ~ observableEF (*hf*) ef),
      eval_builtin_args ge rs sp m args vargs ->
      external_call ef ge vargs m t vres m' ->
      rs' = Locmap.setres res vres (undef_regs (destroyed_by_builtin ef) rs) ->
      step (Block s f sp (Lbuiltin ef args res :: bb) rs rty) m
         (*t*) (Block s f sp bb rs' rty) m'
  | exec_Lbranch: forall s f sp pc bb rs m rty,
      step (Block s f sp (Lbranch pc :: bb) rs rty) m
        (*E0*) (State s f sp pc rs rty) m
  | exec_Lcond: forall s f sp cond args pc1 pc2 bb rs b pc rs' m rty,
      eval_condition cond (reglist rs args) m = Some b ->
      pc = (if b then pc1 else pc2) ->
      rs' = undef_regs (destroyed_by_cond cond) rs ->
      step (Block s f sp (Lcond cond args pc1 pc2 :: bb) rs rty) m
        (*E0*) (State s f sp pc rs' rty) m
  | exec_Ljumptable: forall s f sp arg tbl bb rs m n pc rs' rty,
      rs (R arg) = Vint n ->
      list_nth_z tbl (Int.unsigned n) = Some pc ->
      rs' = undef_regs (destroyed_by_jumptable) rs ->
      step (Block s f sp (Ljumptable arg tbl :: bb) rs rty) m
        (*E0*) (State s f sp pc rs' rty) m
  | exec_Lreturn: forall s f sp bb rs m m' rty,
      Mem.free m sp 0 f.(fn_stacksize) = Some m' ->
      step (Block s f (Vptr sp Int.zero) (Lreturn :: bb) rs rty) m
        (*E0*) (Returnstate s (return_regs (parent_locset s) rs) rty) m'
  | exec_function_internal: forall s f rs m m' sp rs' rty,
      Mem.alloc m 0 f.(fn_stacksize) = (m', sp) ->
      rs' = undef_regs destroyed_at_function_entry (call_regs rs) ->
      step (Callstate s (Internal f) rs rty) m
        (*E0*) (State s f (Vptr sp Int.zero) f.(fn_entrypoint) rs' rty) m'
  | exec_function_external: forall s ef t args res rs m rs' m' rty
      (*COMPCOMP adaptation: restrict to helper functions*)(OBS: EFisHelper (*hf*) ef),
      args = map (fun p => Locmap.getpair p rs) (loc_arguments (ef_sig ef)) ->
      external_call ef ge args m t res m' ->
      rs' = Locmap.setpair (loc_result (ef_sig ef)) res rs ->
      step (Callstate s (External ef) rs rty) m
         (*t*) (Returnstate s rs' rty) m'
  | exec_return: forall f sp rs1 bb s rs m rty,
      step (Returnstate (Stackframe f sp rs1 bb :: s) rs rty) m
        (*E0*) (Block s f sp bb rs rty) m.

End RELSEM.

(** Execution of a whole program boils down to invoking its main
  function.  The result of the program is the return value of the
  main function, to be found in the machine register dictated
  by the calling conventions. *)
(*
Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall b f m0,
      let ge := Genv.globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      funsig f = signature_main ->
      initial_state p (Callstate nil f (Locmap.init Vundef) m0).

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall rs m retcode,
      Locmap.getpair (map_rpair R (loc_result signature_main)) rs = Vint retcode ->
      final_state (Returnstate nil rs m) retcode.

Definition semantics (p: program) :=
  Semantics step (initial_state p) final_state (Genv.globalenv p).
*)

(** COMPCOMP NEW SECTION: Building a MemSem semantics *)

(*CompComp new*) 
Function setlocs (rl: list loc) (vl: list val) (rs: Locmap.t): option Locmap.t:=
match vl with
  | v1::vl0 => match rl with nil => None | r1 :: rl0 => 
                          match setlocs rl0 vl0 rs with None => None 
                          | Some r => Some (Locmap.set r1 v1 r)
                          end
               end
  | nil => match rl with nil => Some rs | _ => None end
end.

Definition LTL_initial_core (ge:genv) (v: val) (args:list val): option state :=
   match v with
     | Vptr b i => 
          if Int.eq_dec i Int.zero 
          then match Genv.find_funct_ptr ge b with
                 | None => None
                 | Some f => 
                    match f with Internal fi =>
                     let tyl := sig_args (funsig f) in
                     if val_has_type_list_func args (sig_args (funsig f))
                        && vals_defined args
                        && zlt (4*(2*(Zlength args))) Int.max_unsigned
                     then match setlocs (regs_of_rpairs (loc_arguments (funsig f))) args (Locmap.init Vundef)
                          with None => None
                            | Some rs => Some (Callstate
                                      nil
                                      f 
                                      rs
                                      (sig_res (funsig f)))
                          end
                     else None
                   | External _ => None
                   end
               end
          else None
     | _ => None
    end.

Definition LTL_at_external (c: state) 
  : option (external_function * signature * list val) :=
  match c with
    | State _ _ _ _ _ _ => None
    | Block _ _ _ _ _ _ => None
    | Callstate s f rs retty => 
      match f with
        | Internal f => None
        | External ef => 
           if observableEF_dec (*hf*) ef 
           then Some (ef, ef_sig ef, map (fun p => Locmap.getpair p rs) (loc_arguments (ef_sig ef)))
               (*in CompComp2.1, had this:decode_longs (sig_args (ef_sig ef)) 
                                     (map rs (loc_arguments (ef_sig ef))))*)
           else None
      end
    | Returnstate _ _ _ => None
 end.

Definition LTL_after_external (vret: option val) (c: state) : option state :=
  match c with 
    | Callstate s f rs retty => 
      match f with
        | Internal f => None
        | External ef => 
          match vret with
            | None => Some (Returnstate s 
                (Locmap.setpair (loc_result (ef_sig ef)) Vundef rs)
                (sig_res (ef_sig ef)))
            | Some v => Some (Returnstate s 
                (Locmap.setpair (loc_result (ef_sig ef)) v rs)
                (sig_res (ef_sig ef)))
          end
      end
    | _ => None
  end.
(*In CompComp2.1, had this:
Definition LTL_after_external (vret: option val) (c: state) : option state :=
  match c with 
    | Callstate s f rs retty => 
      match f with
        | Internal f => None
        | External ef => 
          match vret with
            | None => Some (Returnstate s (sig_res (ef_sig ef))
                (Locmap.setlist (map R (loc_result (ef_sig ef))) 
                  (encode_long (sig_res (ef_sig ef)) Vundef) rs) retty)
            | Some v => Some (Returnstate s (sig_res (ef_sig ef))
                (Locmap.setlist (map R (loc_result (ef_sig ef))) 
                  (encode_long (sig_res (ef_sig ef)) v) rs) retty) 
          end
      end
    | _ => None
  end.
*)

(*CompComp: TODO: support other calling convnetions -- maybe cconv should be another
  argument of Returnstate constructor?*)
Definition LTL_halted (q : state): option val :=
  match q with 
  Returnstate nil ls rty =>
    Some (Locmap.getpair (map_rpair R (loc_result (mksignature nil rty cc_default))) ls)
| _ => None
  end.
(*In compComp2.1 had this:
Definition LTL_halted (q : LTL_core): option val :=
    match q with 
      (*Return Tlong, which must be decoded*)
      | LTL_Returnstate nil _ rs (Some Tlong) => 
           match loc_result (mksignature nil (Some Tlong)) with
             | nil => None
             | r1 :: r2 :: nil => 
                 match decode_longs (Tlong::nil) (rs (R r1)::rs (R r2)::nil) with
                   | v :: nil => Some v
                   | _ => None
                 end
             | _ => None
           end

      (*Return a value of any other typ*)
      | LTL_Returnstate nil _ rs (Some retty) =>
           match loc_result (mksignature nil (Some retty)) with
            | nil => None
            | r :: TL => match TL with 
                           | nil => Some (rs (R r))
                           | _ :: _ => None
                         end
           end

      (*Return Tvoid - modeled as integer return*)
      | LTL_Returnstate nil _ rs None => Some (rs (R AX))

      | _ => None
    end.*)

Lemma ltl_step_not_external: forall (ge : genv) m q m' q',
      step ge q m q' m' -> LTL_at_external q = None.
Proof.
  intros. inv H; try reflexivity. 
  simpl. destruct (observableEF_dec (*hf*) ef); simpl; trivial. 
  eelim EFhelpers; eassumption. 
Qed.

Lemma ltl_step_not_halted: forall (ge : genv) m q m' q',
      step ge q m q' m' -> LTL_halted q = None.
Proof. intros. inv H; try reflexivity. Qed.

Lemma ltl_external_xor_halted: forall q, 
      LTL_at_external q = None \/ LTL_halted q = None.
Proof.
  destruct q; simpl; try (left; reflexivity); try (right; reflexivity).
Qed.

Lemma ltl_after_xor_at_external: forall (retv : option val) q q',
      LTL_after_external retv q = Some q' -> LTL_at_external q' = None.
Proof.
  intros. destruct q; destruct q'; try destruct f; destruct retv; simpl in *; try discriminate; try reflexivity.
Qed.

Require Import sepcomp.semantics.
Require Import sepcomp.semantics_lemmas.

Definition LTL_core_sem : CoreSemantics genv state mem.
Proof.
  eapply (@Build_CoreSemantics _ _ _ 
            LTL_initial_core
            LTL_at_external
            LTL_after_external
            LTL_halted
            step).
  apply ltl_step_not_external.
  apply ltl_step_not_halted. 
  apply ltl_external_xor_halted.
Defined.

Lemma ltl_step_mem : forall g c m c' m' (CS: step g c m c' m'), mem_step m m'.
Proof. intros.
       inv CS; try apply mem_step_refl.
       + (*Storev*)
          destruct a; simpl in H0; inv H0. 
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

Program Definition LTL_mem_sem : MemSem genv state.
Proof.
apply Build_MemSem with (csem := LTL_core_sem).
  apply ltl_step_mem.
Defined.

(** * Operations over LTL *)

(** Computation of the possible successors of a block.
  This is used in particular for dataflow analyses. *)

Fixpoint successors_block (b: bblock) : list node :=
  match b with
  | nil => nil                          (**r should never happen *)
  | Ltailcall _ _ :: _ => nil
  | Lbranch s :: _ => s :: nil
  | Lcond _ _ s1 s2 :: _ => s1 :: s2 :: nil
  | Ljumptable _ tbl :: _ => tbl
  | Lreturn :: _ => nil
  | instr :: b' => successors_block b'
  end.

(** COMPCOMP NEW SECTION: Building an Effect semantics *)
Require Import sepcomp.effect_semantics.
Require Import sepcomp.mem_lemmas.

Section EFFSEM.

Variable ge: genv.

Inductive estep: (block -> Z -> bool) -> state -> mem -> state -> mem -> Prop :=
  | effexec_start_block: forall s f sp pc rs m bb rty,
      (fn_code f)!pc = Some bb ->
      estep EmptyEffect (State s f sp pc rs rty) m
        (*E0*) (Block s f sp bb rs rty) m
  | effexec_Lop: forall s f sp op args res bb rs m v rs' rty,
      eval_operation ge sp op (reglist rs args) m = Some v ->
      rs' = Locmap.set (R res) v (undef_regs (destroyed_by_op op) rs) ->
      estep EmptyEffect (Block s f sp (Lop op args res :: bb) rs rty) m
        (*E0*) (Block s f sp bb rs' rty) m
  | effexec_Lload: forall s f sp chunk addr args dst bb rs m a v rs' rty,
      eval_addressing ge sp addr (reglist rs args) = Some a ->
      Mem.loadv chunk m a = Some v ->
      rs' = Locmap.set (R dst) v (undef_regs (destroyed_by_load chunk addr) rs) ->
      estep EmptyEffect (Block s f sp (Lload chunk addr args dst :: bb) rs rty) m
        (*E0*) (Block s f sp bb rs' rty) m
  | effexec_Lgetstack: forall s f sp sl ofs ty dst bb rs m rs' rty,
      rs' = Locmap.set (R dst) (rs (S sl ofs ty)) (undef_regs (destroyed_by_getstack sl) rs) ->
      estep EmptyEffect (Block s f sp (Lgetstack sl ofs ty dst :: bb) rs rty) m
        (*E0*) (Block s f sp bb rs' rty) m
  | effexec_Lsetstack: forall s f sp src sl ofs ty bb rs m rs' rty,
      rs' = Locmap.set (S sl ofs ty) (rs (R src)) (undef_regs (destroyed_by_setstack ty) rs) ->
      estep EmptyEffect (Block s f sp (Lsetstack src sl ofs ty :: bb) rs rty) m
        (*E0*) (Block s f sp bb rs' rty) m
  | effexec_Lstore: forall s f sp chunk addr args src bb rs m a rs' m' rty,
      eval_addressing ge sp addr (reglist rs args) = Some a ->
      Mem.storev chunk m a (rs (R src)) = Some m' ->
      rs' = undef_regs (destroyed_by_store chunk addr) rs ->
      estep (StoreEffect a (encode_val chunk (rs (R src))))
         (Block s f sp (Lstore chunk addr args src :: bb) rs rty) m
        (*E0*) (Block s f sp bb rs' rty) m'
  | effexec_Lcall: forall s f sp sig ros bb rs m fd rty,
      find_function ge ros rs = Some fd ->
      funsig fd = sig ->
      estep EmptyEffect (Block s f sp (Lcall sig ros :: bb) rs rty) m
        (*E0*) (Callstate (Stackframe f sp rs bb :: s) fd rs rty) m
  | effexec_Ltailcall: forall s f sp sig ros bb rs m fd rs' m' rty,
      rs' = return_regs (parent_locset s) rs ->
      find_function ge ros rs' = Some fd ->
      funsig fd = sig ->
      Mem.free m sp 0 f.(fn_stacksize) = Some m' ->
      estep (FreeEffect m 0 (f.(fn_stacksize)) sp) 
            (Block s f (Vptr sp Int.zero) (Ltailcall sig ros :: bb) rs rty) m
        (*E0*) (Callstate s fd rs' rty) m'
  | effexec_Lbuiltin: forall s f sp ef args res bb rs m vargs t vres rs' m' rty 
      (*COMPCOMP adaptation: limit to unobervables:*) (NOBS: ~ observableEF (*hf*) ef),
      eval_builtin_args ge rs sp m args vargs ->
      external_call ef ge vargs m t vres m' ->
      rs' = Locmap.setres res vres (undef_regs (destroyed_by_builtin ef) rs) ->
      estep (BuiltinEffect ge ef vargs m)
               (Block s f sp (Lbuiltin ef args res :: bb) rs rty) m
         (*t*) (Block s f sp bb rs' rty) m'
  | effexec_Lbranch: forall s f sp pc bb rs m rty,
      estep EmptyEffect (Block s f sp (Lbranch pc :: bb) rs rty) m
        (*E0*) (State s f sp pc rs rty) m
  | effexec_Lcond: forall s f sp cond args pc1 pc2 bb rs b pc rs' m rty,
      eval_condition cond (reglist rs args) m = Some b ->
      pc = (if b then pc1 else pc2) ->
      rs' = undef_regs (destroyed_by_cond cond) rs ->
      estep EmptyEffect (Block s f sp (Lcond cond args pc1 pc2 :: bb) rs rty) m
        (*E0*) (State s f sp pc rs' rty) m
  | effexec_Ljumptable: forall s f sp arg tbl bb rs m n pc rs' rty,
      rs (R arg) = Vint n ->
      list_nth_z tbl (Int.unsigned n) = Some pc ->
      rs' = undef_regs (destroyed_by_jumptable) rs ->
      estep EmptyEffect (Block s f sp (Ljumptable arg tbl :: bb) rs rty) m
        (*E0*) (State s f sp pc rs' rty) m
  | effexec_Lreturn: forall s f sp bb rs m m' rty,
      Mem.free m sp 0 f.(fn_stacksize) = Some m' ->
      estep (FreeEffect m 0 (f.(fn_stacksize)) sp)
            (Block s f (Vptr sp Int.zero) (Lreturn :: bb) rs rty) m
        (*E0*) (Returnstate s (return_regs (parent_locset s) rs) rty) m'
  | effexec_function_internal: forall s f rs m m' sp rs' rty,
      Mem.alloc m 0 f.(fn_stacksize) = (m', sp) ->
      rs' = undef_regs destroyed_at_function_entry (call_regs rs) ->
      estep EmptyEffect (Callstate s (Internal f) rs rty) m
        (*E0*) (State s f (Vptr sp Int.zero) f.(fn_entrypoint) rs' rty) m'
  | effexec_function_external: forall s ef t args res rs m rs' m' rty
      (*COMPCOMP adaptation: restrict to helper functions*)(OBS: EFisHelper (*hf*) ef),
      args = map (fun p => Locmap.getpair p rs) (loc_arguments (ef_sig ef)) ->
      external_call ef ge args m t res m' ->
      rs' = Locmap.setpair (loc_result (ef_sig ef)) res rs ->
      estep (BuiltinEffect ge ef args m) (Callstate s (External ef) rs rty) m
         (*t*) (Returnstate s rs' rty) m'
  | effexec_return: forall f sp rs1 bb s rs m rty,
      estep EmptyEffect (Returnstate (Stackframe f sp rs1 bb :: s) rs rty) m
        (*E0*) (Block s f sp bb rs rty) m.

Lemma ltl_effax1: forall (E : block -> Z -> bool) c m c' m',
      estep E c m c' m' ->
      (corestep (LTL_mem_sem (*hf*)) ge c m c' m' /\
       Mem.unchanged_on (fun b ofs => E b ofs = false) m m').
Proof. 
intros.
  induction H.
  split. eapply exec_start_block; eassumption.
         apply Mem.unchanged_on_refl.
  split. eapply exec_Lop; eassumption. 
         apply Mem.unchanged_on_refl.
  split. eapply exec_Lload; eassumption. 
         apply Mem.unchanged_on_refl.
  split. eapply exec_Lgetstack; eassumption. 
         apply Mem.unchanged_on_refl.
  split. eapply exec_Lsetstack; eassumption. 
         apply Mem.unchanged_on_refl.
  split. eapply exec_Lstore; eassumption. 
         eapply StoreEffect_Storev; eassumption.
  split. eapply exec_Lcall; eassumption. 
         apply Mem.unchanged_on_refl.
  split. eapply exec_Ltailcall; eassumption. 
         eapply FreeEffect_free; eassumption. 
  split. econstructor; eassumption.
         eapply BuiltinEffect_unchOn; try eassumption.
(*  split. unfold corestep, coopsem; simpl. 
         eapply ltl_corestep_exec_Ibuiltin; eassumption.
         eapply ec_builtinEffectPolymorphic; eassumption.*)
  split. eapply exec_Lbranch; eassumption. 
         apply Mem.unchanged_on_refl.
  split. eapply exec_Lcond; eassumption. 
         apply Mem.unchanged_on_refl.
  split. eapply exec_Ljumptable; eassumption. 
         apply Mem.unchanged_on_refl.
  split. eapply exec_Lreturn; eassumption. 
         eapply FreeEffect_free; eassumption. 
  split. eapply exec_function_internal; eassumption.
         eapply Mem.alloc_unchanged_on; eassumption. 
  split. eapply exec_function_external; eassumption.
         eapply BuiltinEffect_unchOn; try eassumption. 
         eapply EFhelpers; eassumption.
  split. eapply exec_return; eassumption.
         apply Mem.unchanged_on_refl.
Qed.

Lemma ltl_effax2: forall c m c' m',
      step ge c m c' m' ->
      exists E, estep E c m c' m'.
Proof.
intros. inv H.
    eexists. eapply effexec_start_block; eassumption.
    eexists. eapply effexec_Lop; eauto.
    eexists. eapply effexec_Lload; eauto.
    eexists. eapply effexec_Lgetstack; eauto.
    eexists. eapply effexec_Lsetstack; eauto.
    eexists. eapply effexec_Lstore; eauto.
    eexists. eapply effexec_Lcall; eauto.
    eexists. eapply effexec_Ltailcall; eauto.
    eexists. eapply effexec_Lbuiltin; eauto.
    eexists. eapply effexec_Lbranch; eauto.
    eexists. eapply effexec_Lcond; eauto.
    eexists. eapply effexec_Ljumptable; eauto.
    eexists. eapply effexec_Lreturn; eassumption.
    eexists. eapply effexec_function_internal; eauto.
    eexists. eapply effexec_function_external; eauto.
    eexists. eapply effexec_return.
Qed.

Lemma ltl_eff_perm: forall (E : block -> Z -> bool) c m c' m'
  (H: estep E c m c' m') b z (HE: E b z = true), Mem.perm m b z Cur Writable.
intros. inv H; try solve [unfold EmptyEffect in HE; simpl in HE; discriminate].
+ eapply storev_curWR; eassumption.
+ eapply free_curWR; eassumption.
+ eapply BuiltinEffect_CurWR; eassumption. 
+ eapply free_curWR; eassumption.
+ eapply BuiltinEffect_CurWR; eassumption. 
Qed. 

End EFFSEM.

Program Definition LTL_eff_sem : @EffectSem genv state.
Proof.
eapply Build_EffectSem with (sem := LTL_mem_sem (*hf*))(effstep:=estep).
intros. eapply ltl_effax1; eassumption.
apply ltl_effax2.
intros. eapply ltl_eff_perm; eassumption.
Defined.

