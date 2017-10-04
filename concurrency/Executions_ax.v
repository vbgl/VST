(** * Definition of axiomatic executions and their validity *)

Require Import concurrency.Machine_ax.
Require Import Coq.Sets.Ensembles.
Require Import concurrency.Ensembles_util.
Require Import concurrency.Relations_util.
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
  Import AxSem.
  Import Order Enumerate.
  Class Execution `{lbl:Labels} :=
    { lab    : id -> ConcLabels;
      thread : id -> tid
    }.

  Notation events := (Ensemble id).

  Section Semantics.
    
    Context
      {Lab : Labels}
      {sem : Semantics}
      {threadpool : ThreadPool C}
      {exec : Execution}.

    Variable cstep: G -> C -> C -> list E -> Prop.
  
    Infix " \ " := (Setminus id) (at level 70, no associativity) : Execution_scope.

    Open Scope Execution_scope.

    Inductive Rstep (genv:G) (po R : relation id) (tp : t) : events -> t -> events -> Prop :=
    | RStep: forall (Ex es : events) e' es' tp'
               (Henum: enumerate po es (e' :: es'))
               (Hmin: e' \in (min R (Union _ Ex es)))
               (Hincl: inclusion _ po R)
               (Hdis: Disjoint _ Ex es)
               (Hstep: @step _ _ _ cstep genv tp (thread e') (List.map lab (e' :: es')) tp'),
        Rstep genv po R tp (Union _ Ex es) tp' Ex.

    Definition step_po (genv:G) po tp Ex tp' Ex' :=
      Rstep genv po po tp Ex tp' Ex'.

  End Semantics.
End Execution.


(** * Valid executions under SC *)
Module ValidSC.

  Import Execution.
  Import Order Enumerate.

  Section ValidSC.
    Context {lbl : Labels}.
    Context {exec : Execution}.

    (** ** Definition of the SC model *)

    (** Definition of well-formed program order*)
    Record po_well_formed (po: relation id) :=
      { (** [po] is a strict partial order *)
        po_strict_PO : strict_partial_order po;
        (** events on the same thread are related by [po] *)
        po_same_thread : forall e1 e2, thread e1 = thread e2 ->
                                  e1 <> e2 ->
                                  po e1 e2 \/ po e2 e1;
        (** Thread spawning induces [po] order between parent-children threads*)
        po_spawn : forall e1 e2,
            lab e1 = Spawn (thread e2) ->
            po e1 e2
      }.

    Definition lab := lab.
    Coercion lab : id >-> ConcLabels.

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
        - [po] is defined on elements of the execution only
        - [sc] is a total strict order over all events
        - [po] is included in [sc]
        - reads read from the latest write before them according to [sc]
        - all accesses have the same size. *)
    (* are accesses aligned? our threadwise semantics only support aligned
       accesses so it can be proven as a corollary, but should we require it of
       valid executions? *)
    Record validSC (Ex : events) (po sc : relation id) :=
      { wf_po    : po_well_formed po;
        po_onto : forall e1 e2, po e1 e2 -> e1 \in Ex /\ e2 \in Ex;
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


    (** ** Projection Lemmas on records *)
    Lemma po_well_formed_PO {R: relation id} :
      po_well_formed R ->
      strict_partial_order R.
    Proof.
      intro STO;
        now destruct STO.
    Qed.

    Lemma po_well_formed_thread {R: relation id} :
      po_well_formed R ->
      forall e1 e2, thread e1 = thread e2 ->
               e1 <> e2 ->
               R e1 e2 \/ R e2 e1.
    Proof.
      intro STO;
        now destruct STO.
    Qed.

    Lemma po_well_formed_spawn {R: relation id} :
      po_well_formed R ->
      forall e1 e2,
        lab e1 = Spawn (thread e2) ->
        R e1 e2.
    Proof.
      intro STO;
        now destruct STO.
    Qed.

   
  End ValidSC.
  (*NOTE: Why can't I use po_well_formed_spawn as a hint? *)
  Hint Resolve
       po_well_formed_PO po_well_formed_thread : Po_db.
End ValidSC.
        
