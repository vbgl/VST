Require Import concurrency.Asm_core. (* for AxiomaticCoreSem.
                            TODO: Move it out of there and
                            stop importing Asm_core *)
Require Import compcert.common.Values.
Require Import compcert.common.AST.
Import List.
Import List.ListNotations.
Import AxCoreSem.


(** Thread identifiers -- assume natural numbers *)
Notation tid := nat. 

(** Class of threadwise semantics *)
Class Semantics :=
 {
   G: Type; (** Type of global environment *)
   C: Type; (** Type of state/core *)
   E: Type; (** Type of events *)
   Sem: @AxiomaticCoreSemantics G C E (** Threadwise semantics *)
 }.

Class ThreadPool (Sem : Semantics) :=
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

Notation "tp # i " := (getThread i tp) (at level 1) : Ax_scope.
Notation "tp <- i , c" := (updThread i c tp) (at level 1) : Ax_scope.
Notation tstep := (corestep Sem).

(** Definition of a generic axiomatic concurrency machine *)
Module AxSem.
Section AxSem.

  Context {sem : Semantics}
          {threadpool : ThreadPool sem}.
  
  (* Instance FunPool : ThreadPool. *)
  (* Proof. *)
  (*   eapply Build_ThreadPool with *)
  (*   (t := nat -> option C) *)
  (*     (getThread := fun i tp => tp i) *)
  (*     (updThread := fun i c tp => *)
  (*                     fun j => if (PeanoNat.Nat.eq_dec i j) *)
  (*                           then Some c else tp j). *)
  (*   - intros. *)
  (*     unfold getThread, updThread. *)
  (*     destruct eq_dec.EqDec_nat; subst; *)
  (*       [exfalso|]; now auto. *)
  (*   - intros. *)
  (*     unfold getThread, updThread. *)
  (*     destruct (PeanoNat.Nat.eq_dec i i); now tauto. *)
  (* Defined. *)

  (** Parameterized over external (concurrent) steps*)
  Variable cstep: G -> t -> tid -> list E -> t -> Prop.

  Inductive step {genv:G} (tp : t) (i: tid): list E -> t -> Prop :=
  | InternalStep:
      forall c c' evl
        (Hget: getThread i tp = Some c)
        (Hstep: tstep genv c c' evl),
        step tp i evl (updThread i c' tp)
  | ExternalStep:
      forall  evl tp'
         (Hcstep: cstep genv tp i evl tp'),
        step tp i evl tp'.

End AxSem.
End AxSem.

Require Import compcert.lib.Integers.
Import Int.

(** Definition of an axiomatic concurrency machine consisting of lock operations *)
Module AxLockMachine.
Section AxLockMachine.

  (** Externals symbols and signatures. *)
  Notation EXIT :=
    (EF_external "EXIT" (mksignature (AST.Tint::nil) None)).

  Notation CREATE_SIG := (mksignature (AST.Tint::AST.Tint::nil) None cc_default).
  Notation CREATE := (EF_external "spawn" CREATE_SIG).

  Notation MKLOCK :=
    (EF_external "makelock" (mksignature (AST.Tint::nil) None cc_default)).
  Notation FREELOCK :=
    (EF_external "freelock" (mksignature (AST.Tint::nil) None cc_default)).

  Notation LOCK_SIG := (mksignature (AST.Tint::nil) None cc_default).
  Notation LOCK := (EF_external "acquire" LOCK_SIG).
  Notation UNLOCK_SIG := (mksignature (AST.Tint::nil) None cc_default).
  Notation UNLOCK := (EF_external "release" UNLOCK_SIG).

  (** Assume some threadwise semantics*)
  Context {sem: Semantics}.

  (** Parameterize over the events generated for each step of the
      Lock machine (e.g. x86 generates different events than Power) *)
  Class LockSem :=
    { lockE     : block -> int -> list E; (** Given the lock address *) 
      unlockE   : block -> int -> list E; 
      mklockE   : block -> int -> list E;
      freelockE : block -> int -> list E;
      spawnE    : block -> int -> val -> tid -> list E (** Given the address of the code to be executed
                                                  an argument passed by parent thread and
                                                  the tid of the new thread*)
     }.
  
  Context {threadpool: ThreadPool sem}
          {lockSem: LockSem}.

  Open Scope Ax_scope.
  (** Concurrent steps of the lock machine *)
  Inductive cstep {genv:G} (tp : t) (i : tid): list E -> t -> Prop :=
  | StepAcq:
      forall c c' b ofs evargs
        (Hcode: tp # i = Some c)
        (Hat_external: at_external Sem genv c LOCK ((Vptr b ofs) :: nil) evargs)
        (Hafter_external: after_external Sem genv None c = Some c'),
        cstep tp i (evargs ++ (lockE b ofs)) (tp <- i,c')
  | StepRel:
      forall c c' b ofs evargs
        (Hcode: tp # i = Some c)
        (Hat_external: at_external Sem genv c UNLOCK ((Vptr b ofs) :: nil) evargs)
        (Hafter_external: after_external Sem genv None c = Some c'),
        cstep tp i (evargs ++ (unlockE b ofs)) (tp <- i,c')
  | StepMkLock:
      forall c c' b ofs evargs
        (Hcode: tp # i = Some c)
        (Hat_external: at_external Sem genv c MKLOCK ((Vptr b ofs) :: nil) evargs)
        (Hafter_external: after_external Sem genv None c = Some c'),
        cstep tp i (evargs ++ (mklockE b ofs)) (tp <- i,c')
  | StepFreeLock:
      forall c c' b ofs evargs
        (Hcode: tp # i = Some c)
        (Hat_external: at_external Sem genv c FREELOCK ((Vptr b ofs) :: nil) evargs)
        (Hafter_external: after_external Sem genv None c = Some c'),
        cstep tp i (evargs ++ (freelockE b ofs)) (tp <- i,c')
  | StepSpawn:
      forall c c' c'' b ofs arg evargs evinit j
        (Hcode: tp # i = Some c)
        (Hat_external: at_external Sem genv c CREATE ((Vptr b ofs) :: arg :: nil) evargs)
        (Hafter_external: after_external Sem genv None c = Some c')
        (Hinitial: initial_core Sem j genv (Vptr b ofs) [arg] c'' evinit)
        (Hfresh: tp # j = None),
        cstep tp i (evargs ++ (spawnE b ofs arg j)) ((tp <- i,c') <- j,c'').

  Import AxSem.

  Notation step := (step cstep). 

End AxLockMachine.
End AxLockMachine.

