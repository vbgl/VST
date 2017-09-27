Require Import concurrency.Asm_core. (* for AxiomaticCoreSem.
                            TODO: Move it out of there and
                            stop importing Asm_core *)
Require Import compcert.common.Values.
Require Import compcert.common.AST.
Require Import compcert.common.Memdata.
Require Import Coq.ZArith.BinInt.
Require Import compcert.lib.Integers.
Import Int.
Import List.
Import List.ListNotations.
Import AxCoreSem.


(** Thread identifiers -- assume natural numbers *)
Notation tid := nat. 

(** Labels should satisfy this interface *)
Class Labels :=
  { E       :> Type;
    isRead  : E -> bool;
    isWrite : E -> bool;
    loc     : E -> option (block * Z * Z);
    mval    : E -> option (list memval)
  }.

(** Class of threadwise semantics *)
Class Semantics `{lbl:Labels} :=
 {
   G: Type; (** Type of global environment *)
   C: Type; (** Type of state/core *)
   Sem: @AxiomaticCoreSemantics G C E (** Threadwise semantics *)
 }.

Class ThreadPool (C: Type) :=
  {
    t : Type; (** type of thread pool *)
    getThread: tid -> t -> option C; (** get state of thread *)
    updThread: tid -> C -> t -> t; (** set state of thread *)
    gsoThread:
      forall i j tp c (Hneq: i <> j),
        getThread i (updThread j c tp) = getThread i tp;
    gssThread:
      forall i tp c,
        getThread i (updThread i c tp) = Some c
  }.

Notation "tp # i " := (getThread i tp) (at level 1) : tp_scope.
Notation "tp <- i , c" := (updThread i c tp) (at level 1): tp_scope.
Notation threadStep := (corestep Sem).

(** Symbol for thread spawn external *)
Notation CREATE_SIG := (mksignature (AST.Tint::AST.Tint::nil) None cc_default).
Notation CREATE := (EF_external "spawn" CREATE_SIG).

(** Definition of a generic axiomatic concurrency machine *)
Module AxSem.
Section AxSem.

  Context
    {Lab : Labels}
    {sem : Semantics}
    {threadpool : ThreadPool C}.

  Inductive ConcLabels : Type :=
  | Spawn : tid -> ConcLabels
  | Ev    : E -> ConcLabels.

  Definition concLabelsofE (es : list E) :=
    List.map (fun ev => Ev ev) es.

  (** External (sync) steps*)
  Variable syncStep: G -> C ->  C -> list E -> Prop.

  Open Scope tp_scope.
  Inductive step (genv:G) (tp : t) (i: tid): list ConcLabels -> t -> Prop :=
  | ThreadStep:
      forall c c' evl
        (Hget: getThread i tp = Some c)
        (Hstep: threadStep genv c c' evl),
        step genv tp i (concLabelsofE evl) (updThread i c' tp)
  | SyncStep:
      forall  c c' evl
        (Hget: getThread i tp = Some c)
        (Hstep: syncStep genv c c' evl),
        step genv tp i (concLabelsofE evl) (updThread i c' tp)
  | StepSpawn:
      forall c c' c'' b ofs arg evargs evinit j
        (Hcode: tp # i = Some c)
        (Hat_external: at_external Sem genv c CREATE
                                   ((Vptr b ofs) :: arg :: nil) evargs)
        (Hafter_external: after_external Sem genv None c = Some c')
        (Hinitial: initial_core Sem j genv (Vptr b ofs) [arg] c'' evinit)
        (Hfresh: tp # j = None),
        step genv tp i ((concLabelsofE evargs) ++ [Spawn j]) ((tp <- i,c') <- j,c'').

End AxSem.
End AxSem.


(** Definition of an axiomatic concurrency machine consisting of lock operations *)
Module AxLockMachine.

  Import AxSem.
  (** Symbols and signatures for externals of the locks machine. *)
  Notation EXIT :=
    (EF_external "EXIT" (mksignature (AST.Tint::nil) None)).

  Notation MKLOCK :=
    (EF_external "makelock" (mksignature (AST.Tint::nil) None cc_default)).
  Notation FREELOCK :=
    (EF_external "freelock" (mksignature (AST.Tint::nil) None cc_default)).

  Notation LOCK_SIG := (mksignature (AST.Tint::nil) None cc_default).
  Notation LOCK := (EF_external "acquire" LOCK_SIG).
  Notation UNLOCK_SIG := (mksignature (AST.Tint::nil) None cc_default).
  Notation UNLOCK := (EF_external "release" UNLOCK_SIG).

  Section AxLockMachine.

  (** Assume some threadwise semantics*)
  Context 
    {lbl : Labels}
    {sem : Semantics}.

  (** Parameterize over the events generated for each synchronization step
      of the Lock machine (e.g. x86 generates different events than Power) *)
  Class LockSem :=
    { lockE     : block -> int -> list E; (** Given the lock address *) 
      unlockE   : block -> int -> list E; 
      mklockE   : block -> int -> list E;
      freelockE : block -> int -> list E
     }.
  
  Context {threadpool: ThreadPool C}
          {lockSem: LockSem}.

  Open Scope tp_scope.
  (** Sync steps of the lock machine *)
  Inductive syncStep {genv:G} (c:C) : C -> list E -> Prop :=
  | StepAcq:
      forall b ofs evargs c'
        (Hat_external: at_external Sem genv c LOCK ((Vptr b ofs) :: nil) evargs)
        (Hafter_external: after_external Sem genv None c = Some c'),
        syncStep c c' (evargs ++ (lockE b ofs))
  | StepRel:
      forall b ofs evargs c'
        (Hat_external: at_external Sem genv c UNLOCK ((Vptr b ofs) :: nil) evargs)
        (Hafter_external: after_external Sem genv None c = Some c'),
        syncStep c c' (evargs ++ (unlockE b ofs))
  | StepMkLock:
      forall b ofs evargs c'
        (Hat_external: at_external Sem genv c MKLOCK ((Vptr b ofs) :: nil) evargs)
        (Hafter_external: after_external Sem genv None c = Some c'),
        syncStep c c' (evargs ++ (mklockE b ofs))
  | StepFreeLock:
      forall b ofs evargs c'
        (Hat_external: at_external Sem genv c FREELOCK ((Vptr b ofs) :: nil) evargs)
        (Hafter_external: after_external Sem genv None c = Some c'),
        syncStep c c' (evargs ++ (freelockE b ofs)).

End AxLockMachine.
End AxLockMachine.

