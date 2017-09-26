(** * Definition of axiomatic executions and their validity *)

Require Import concurrency.Machine_ax.
Require Import Coq.Sets.Ensembles.
Require Import concurrency.Ensembles_util.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Lists.List.
Require Import compcert.common.Values.
Require Import compcert.common.Memdata.
Require Import Coq.ZArith.BinInt.
Import Relation_Operators.

Inductive stepN {A B: Type} (R : A -> B -> A -> B -> Prop) : nat -> A -> B -> A -> B -> Prop :=
  | Step0 : forall x y, stepN R 0 x y x y
  | StepN : forall n x1 y1 x2 y2 x3 y3
      (HRstep: R x1 y1 x2 y2)
      (HRstepN': stepN R n x2 y2 x3 y3),
      stepN R (S n) x1 y1 x3 y3.

Module Execution.

  Notation id := nat.
  Class Execution (E:Type) :=
    { lab    : id -> E;
      thread : id -> tid
    }.

  Notation events := (Ensemble id).

  Open Scope Ensembles_scope.
  (** Minimum elements in U according to R *)
  Definition min {A:Type} (R: relation A) (U: Ensemble A) : Ensemble A :=
    [ set x | x \in U /\ ~exists y, R y x ].

  Definition immediate {A:Type} (R: relation A) : relation A :=
    fun x y => R x y /\ ~ exists z, R x z /\ R z y.

  (** Enumerate a (finite) set to a list according to the order defined by R *)
  Inductive enumerate {A:Type} (R: relation A) : Ensemble A -> list A -> Prop :=
  | EmptySet: enumerate R (Empty_set _) nil
  | SingletonSet: forall x, enumerate R (Singleton _ x) (x :: nil)
  | ConsSet: forall x y es es'
               (HR: immediate R x y)
               (Henum: enumerate R (Union _ es (Singleton _ y)) (y :: es')),
      enumerate R (Union _ (Union _ es (Singleton _ y)) (Singleton _ x)) (x :: y :: es').

  Section Semantics.
    
    Import AxSem.
    
    Context
      {E : Type}
      {sem : Semantics E}
      {threadpool : ThreadPool C}
      {exec : Execution E}.

    Variable cstep: G -> t -> tid -> list E -> t -> Prop.
  
    Infix " \ " := (Setminus id) (at level 70, no associativity) : Execution_scope.

    Open Scope Execution_scope.

    Inductive Rstep (genv:G) (po R : relation id) (tp : t) : events -> t -> events -> Prop :=
    | RStep: forall (Ex es : events) e' es' tp'
               (Henum: enumerate po es (e' :: es'))
               (Hmin: e' \in (min R (Union _ Ex es)))
               (Hincl: inclusion _ po R)
               (Hstep: @step _ _ _ cstep genv tp (thread e') (List.map lab (e' :: es')) tp'),
        Rstep genv po R tp (Union _ Ex es) tp' Ex.

    Definition step_po (genv:G) po tp Ex tp' Ex' :=
      Rstep genv po po tp Ex tp' Ex'.

  End Semantics.
End Execution.


(** * Valid executions under SC *)
Module ValidSC.

  Import Execution.
  
  (** Labels should satisfy this interface *)
  Class Labels :=
    { E       :> Type;
      isRead  : E -> bool;
      isWrite : E -> bool;
      Spawn   : tid -> E;
      loc     : E -> option (block * Z * Z);
      mval    : E -> option (list memval)
    }.

  Section ValidSC.
    Context {lbl : Labels}.
    Context {exec : Execution E}.


    Record strict_partial_order {A:Type} (R: relation A) :=
      { antisym : antisymmetric _ R;
        trans   : transitive _ R;
        strict  : forall x : A, ~ R x x
      }.

    Record strict_total_order {A:Type} (R: relation A) (U: Ensemble A) :=
      { PO : strict_partial_order R;
        total : forall e1 e2 (Hneq: e1 <> e2)
                  (Hdom: e1 \in U /\ e2 \in U),
            R e1 e2 \/ R e2 e1;
        sc_onto  : forall e1 e2, R e1 e2 -> e1 \in U /\ e2 \in U;
      }.

    (** Definition of well-formed program order*)
    Record po_well_formed (Ex : events) (po: relation id) :=
      {
        (** [po] is defined on elements of the execution only *)
        po_onto : forall e1 e2, po e1 e2 -> e1 \in Ex /\ e2 \in Ex;
        (** [po] is a strict partial order *)
        po_strict_PO : strict_partial_order po;
        (** events on the same thread are related by [po] *)
        po_same_thread : forall e1 e2, thread e1 = thread e2 ->
                                  po e1 e2 \/ po e2 e1;
        (** Thread spawning induces [po] order between parent-children threads*)
        po_spawn : forall e1 e2,
            lab e1 = Spawn (thread e2) ->
            po e1 e2
      }.

    Definition lab := lab.
    Coercion lab : id >-> E.

    (** Validity of read events in the execution:
        - Every read reads from some write that is on
          the same location and has the same value
        - and is ordered before it according to the sc order
        - and there is no other write on the same location between them*) 
    Definition reads_from (sc : relation id) :=
      forall e1 : id, isRead e1 = true ->
            exists e2 : id,
              isWrite e2 = true /\
              loc e1 = loc e2 /\
              mval e1 = mval e2 /\
              sc e2 e1 /\
              ~exists e3, (sc e3 e1 /\ sc e2 e3 /\ loc e1 = loc e3).
    (* Notice that loc e1 = loc e3 is only sound with no mixed-size accesses *)

    (** Valid sequential consistent executions:
        - program order [po] is [po_well_formed]
        - [sc] is a total strict order over all events
        - [po] is included in [sc]
        - reads read from the latest write before them according to [sc]
        - all accesses have the same size. *)
    (* are accesses aligned? our threadwise semantics only support aligned
       accesses so it can be proven as a corollary, but should we require it of
       valid executions? *)
    Record validSC (Ex : events) (po sc : relation id) :=
      { wf_po    : po_well_formed Ex po;
        total_sc : strict_total_order sc Ex;
        po_sc    : inclusion _ po sc;
        rf_sc    : reads_from sc;
        no_mix   : exists sz, forall e1, e1 \in Ex ->
                                match loc e1 with
                                | Some (_, ofs, sz') =>
                                  sz = sz'
                                | None => True
                                end
      }.

  End ValidSC.
End ValidSC.
        
