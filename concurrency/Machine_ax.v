Require Import concurrency.Asm_core. (* for AxiomaticCoreSem.
                            TODO: Move it out of there and
                            stop importing Asm_core *)
Import AxCoreSem.

Class Semantics :=
 {
   G: Type;
   C: Type;
   E:Type;
   Sem: @AxiomaticCoreSemantics G C E
 }.

Class ThreadPool (SEM: Semantics) :=
  {
    tid := nat;
    t : Type;
    getThread: tid -> t -> option C;
    updThread: tid -> C -> t -> t;
    gsoThread:
      forall i j t c (Hneq: i <> j),
        getThread i (updThread j c t) = getThread i t;
    gssThread:
      forall i t c,
        getThread i (updThread i c t) = Some c }.

  Parameter getThread: tid -> t -> option SEM.C.
  Parameter updThread: tid -> SEM.C -> t -> t.
  Parameter gsoThread:
    forall i j t c (Hneq: i <> j),
      getThread i (updThread j c t) = getThread i t.
  Parameter gssThread:
    forall i t c,
      getThread i (updThread i c t) = Some c.
End ThreadPoolSig.

Module ThreadPool <: ThreadPoolSig.

  Declare Module SEM:Semantics.
  Definition tid := nat.
  Definition t := tid -> option SEM.C.

  Definition getThread i (tp: t) := tp i.
  Definition updThread i c (tp : t) :=
    fun j => if (PeanoNat.Nat.eq_dec i j) then Some c else tp j.

  Lemma gsoThread:
    forall i j t c (Hneq: i <> j),
      getThread i (updThread j c t) = getThread i t.
  Proof.
    intros.
    unfold getThread, updThread.
    destruct eq_dec.EqDec_nat; subst;
      [exfalso|]; now auto.
  Qed.

  Lemma gssThread:
    forall i t c,
      getThread i (updThread i c t) = Some c.
  Proof.
    intros.
    unfold getThread, updThread.
    destruct (PeanoNat.Nat.eq_dec i i); now tauto.
  Qed.
End ThreadPool.

Module Type AxMachine (SEM:Semantics)
       (ThreadPool : ThreadPoolSig with Module SEM := SEM).
  Import ThreadPool SEM.

  Notation tstep := (corestep G C E Sem).

  (** Parameterized over external (concurrent) steps*)
  Parameter cstep: G -> t -> tid -> list E -> t -> Prop.

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

End AxMachine.

Module AxLockMachine (SEM:Semantics)
       (ThreadPool : ThreadPoolSig with Module SEM := SEM) <:
  AxMachine SEM ThreadPool.
  Import ThreadPool SEM.

  Parameter lockE: list E.
  Parameter unlockE: list E.
  Parameter mkLockE: list E.
  Parameter 

  Inductive cstep {genv:G} (tp : t) (i : tid): list E
    

