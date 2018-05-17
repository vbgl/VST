Require Import Values.
Require Import Memory.
Require Import AST.
Require Import Globalenvs.
Require Import VST.coarse_sepcomp.coarse_defs.

(** * Interaction Semantics *)

(** NOTE: In the code, we call interaction semantics [CoreSemantics]. *)

(** The [G] type parameter is the type of global environments, the type
   [C] is the type of core states, and the type [E] is the type of
   extension requests. *)

(** [at_external] gives a way to determine when the sequential
   execution is blocked on an extension call, and to extract the
   data necessary to execute the call. *)

(** [after_external] give a way to inject the extension call results
   back into the sequential state so execution can continue. *)

(** [initial_core] produces the core state corresponding to an entry
   point of a module.  The arguments are the genv, a pointer to the
   function to run, and the arguments for that function. *)

(** [halted] indicates when a program state has reached a halted state,
   and what it's exit code/return value is when it has reached such
   a state. *)

(** [corestep] is the fundamental small-step relation for the
   sequential semantics. *)

(** The remaining properties give basic sanity properties which constrain
   the behavior of programs. *)
(** -1 a state cannot be both blocked on an extension call and also step, *)
(** -2 a state cannot both step and be halted, and *)
(** -3 a state cannot both be halted and blocked on an external call. *)

Record CoreSemantics {G C M : Type} : Type :=
  { initial_core : nat -> G -> M -> val -> list val -> option C (*now with memory*)
    (*initial_core : nat -> G -> M -> val -> list val -> option (C* option M)*)
  ; at_external : C -> option (external_function * list val * (option val -> option C)) (*now include afterExternal*)
(*  ; after_external : option val -> C -> option C*)
  ; halted : C -> option val
  ; corestep : G -> C -> M -> C -> M -> Prop

  ; corestep_not_at_external:
      forall ge m q m' q', corestep ge q m q' m' -> at_external q = None
  ; corestep_not_halted:
      forall ge m q m' q', corestep ge q m q' m' -> halted q = None
  ; at_external_halted_excl:
      forall q, at_external q = None \/ halted q = None }.

Arguments CoreSemantics : clear implicits.

Section corestepN.

  Context {G C M:Type} (Sem:@CoreSemantics G C M) (ge:G).

  Fixpoint corestepN (n:nat) : C -> M -> C -> M -> Prop :=
    match n with
      | O => fun c m c' m' => (c,m) = (c',m')
      | S k => fun c1 m1 c3 m3 => exists c2, exists m2,
        corestep Sem ge c1 m1 c2 m2 /\
        corestepN k c2 m2 c3 m3
    end.

  Definition corestep_star c m c' m' := exists n, corestepN n c m c' m'.
(*More lemmas in semantics_lemmas.v*)
End corestepN.


Inductive mem_step m m' : Prop :=
    mem_step_storebytes: forall b ofs bytes,
       Mem.storebytes m b ofs bytes = Some m' -> mem_step m m'
  | mem_step_alloc: forall lo hi b',
       Mem.alloc m lo hi = (m',b') -> mem_step m m'
  | mem_step_freelist: forall l,
       Mem.free_list m l = Some m' -> mem_step m m'
  (*Some non-observable external calls are not a single alloc/free/store-step*)
  | mem_step_trans: forall m'',
       mem_step m m'' -> mem_step m'' m' -> mem_step m m'.

(* Memory semantics are CoreSemantics that are specialized to CompCert memories
   and evolve memory according to mem_step. Previous notion CoopCoreSem is deprecated,
   but for now retained in file CoopCoreSem.v *)
Record MemSem {G C} :=
  { csem :> @CoreSemantics G C mem;
    corestep_mem : forall g c m c' m' (CS: corestep csem g c m c' m'), mem_step m m'
  }.

Arguments MemSem : clear implicits.

Inductive CoarseStepResult {C:Type} :=
  CSR_Ext: C -> mem -> (external_function * list val * (option val -> option C)) -> CoarseStepResult
| CSR_Ret: C -> mem -> val -> CoarseStepResult
| CSR_Div: (nat -> mem) -> CoarseStepResult.

Inductive cstep {G C} (Sem : @MemSem G C) g (c:C) (m:mem):
          @CoarseStepResult C -> Prop:=
  cst_ext: forall c' m' x,
           corestep_star Sem g c m c' m' ->
           at_external Sem c' = Some x ->
           cstep Sem g c m (CSR_Ext c' m' x)
| cst_ret: forall c' m' v,
           corestep_star Sem g c m c' m' ->
           halted Sem c' = Some v ->
           cstep Sem g c m (CSR_Ret c' m' v) 
| cst_div: forall  (ci: nat -> C) (mi: nat -> mem)
               (Steps: forall i, corestep Sem g (ci i) (mi i) (ci (S i)) (mi (S i)))
               (H: (ci O, mi O) = (c,m)),
           cstep Sem g c m (CSR_Div mi).
(*Maybe it's preferable to use the following definition and then derive msr_div?
| csr_div': forall (ci: nat -> C) (mi: nat -> mem)
               (Steps: forall i, corestepN Sem g (S i) c m (ci (S i)) (mi (S i)))
               (H: (ci O, mi O) = (c,m)),
           cstep Sem g c m (SCR_Div mi).

Lemma cst_div {G C} (Sem : @MemSem G C) g (c:C) (m:mem): 
      forall (ci: nat -> C) (mi: nat -> mem)
               (Steps: forall i, corestep Sem g (ci i) (mi i) (ci (S i)) (mi (S i)))
               (H: (ci O, mi O) = (c,m)),
      step Sem g c m (CSR_Div mi).
Proof. intros. inv H. specialize (steps_iter _ _ _ _ Steps); intros; clear Steps.
  eapply csr_div'; eauto. 
Qed.*)
