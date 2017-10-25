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

Lemma stepN_trans:
  forall {A B : Type} {R: A -> B -> A -> B -> Prop} k l m x y x' y' x'' y''
    (Hm: m = k + l)
    (HstepK: stepN R k x y x' y')
    (HstepL: stepN R l x' y' x'' y''),
    stepN R m x y x'' y''.
Proof.
  intros A B R k.
  induction k; intros.
  - inv HstepK.
    simpl.
    now auto.
  - inv HstepK.
    econstructor;
      now eauto.
Qed.

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
            po e1 e2;
        po_spec : forall e1 e2, immediate po e1 e2 -> lab e1 = Spawn (thread e2) \/ thread e1 = thread e2
      }.

    Definition lab := lab.
    Coercion lab : id >-> ConcLabels.

    Section ReadsFrom.
    (** Validity of read events in the execution:
        - Every read reads from some write that is on
          the same location and has the same value
        - and is ordered before it according to the sc order
        - and there is no other write on the same location between them*)

    Definition included (slice footprint: Z*Z) : Prop :=
      forall ofs, Intv.In ofs slice -> Intv.In ofs footprint.

    Definition in_slice (ofs : Z) (slice : Z*Z) : Prop :=
      Intv.In ofs slice.

    Variable rf : id -> id -> Z*Z -> Prop.

    Definition rf_valid : Prop :=
      (** forall e1 e2 that are in the reads-from relation under slice *)
      forall (e1 e2 : id) (slice: Z*Z),
        rf e1 e2 slice ->

      (** e1 will be a write and e2 a read*)
        exists (pf1 : isWrite e1 = true)
          (pf2 : isRead e2 = true),

      (** the slice relating them is included in the footprints of both *)
        let '(b1, ofs1, sz1) := loc (or_introl pf1) in
        let '(b2, ofs2, sz2) := loc (or_intror pf2) in
        b1 = b2 /\
        included slice (ofs1, ofs1 + sz1)%Z /\
        included slice (ofs2, ofs2 + sz2)%Z /\

      (** and their values are per-byte equal on each byte of the slice*)
        forall ofs', in_slice ofs' slice ->
                List.nth (Z.to_nat (ofs' - ofs1)%Z) (mval (or_introl pf1)) Undef =
                List.nth (Z.to_nat (ofs' - ofs2)%Z) (mval (or_intror pf2)) Undef.
        
    Definition reads_from_wf : Prop :=
      (** for every read event *)
      forall (er : id) (Hisread:isRead er = true),
        
      (** there exists writes and slices of that writes *)
      exists ws : list (id * (Z*Z)),

        (** such that the slices of every two writes are disjoint *)
        (forall w1 w2,
            List.In w1 ws /\ List.In w2 ws ->
            Intv.disjoint (snd w1) (snd w2)) /\

        (** and every write+slice in the list is rf-related with the read*)
        (forall w, List.In w ws ->
              rf (fst w) er (snd w)) /\

        (** and all bytes in the footprint of the read belong to some slice in the list,
            i.e. the read is fully determined *)
        (forall ofs',
            let '(b, ofs, sz) := loc (or_intror Hisread) in
            Intv.In ofs' (ofs, ofs + sz)%Z <->
            exists w, List.In w ws /\ Intv.In ofs' (snd w)).

    Lemma rf_isWrite:
      forall (Hvalid: rf_valid) {ew er slice}
        (Hrf: rf ew er slice),
        isWrite ew = true.
    Proof.
      intros.
      destruct (Hvalid _ _ _ Hrf) as [? ?];
        now assumption.
    Qed.


    Definition reads_from_sc (sc : relation id) (Hvalid: rf_valid) : Prop :=
      (** if [er] reads [slice] from [ew] and ofs' is one of the bytes read*)
      forall ew er slice
        (Hrf: rf ew er slice)
        ofs'
        (Hofs': Intv.In ofs' slice),

        (** then (ew, er) \in scr: ew is immediately before er in the sc order, between all writes that write this byte *)
        immediate (restr sc (fun x => exists (isWrite_x: isWrite x = true),
                                 let '(bx, ofsx, szx) := loc (or_introl isWrite_x) in
                                 let '(b, ofs, sz) := loc (or_introl (rf_isWrite Hvalid Hrf)) in
                                 b = bx /\ Intv.In ofs' (ofsx, ofsx + szx)%Z)) ew er.

    End ReadsFrom.

    (** Valid sequential consistent executions:
        - program order [po] is [po_well_formed]
        - [po] is defined on elements of the execution only
        - [sc] is a total strict order over all events
        - [po] is included in [sc]
        - specification of [rf]
        - [rf] is well formed, i.e. all the reads read from some writes.
        - reads read from the latest write before them according to [sc]
        - all accesses have the same size. *)
    (* are accesses aligned? our threadwise semantics only support aligned
       accesses so it can be proven as a corollary, but should we require it of
       valid executions? *)
    Record validSC (Ex : events) (po sc : relation id) (rf: id -> id -> Z * Z -> Prop) :=
      { wf_po    : po_well_formed po;
        po_onto  : forall e1 e2, po e1 e2 -> e1 \in Ex /\ e2 \in Ex;
        total_sc : strict_total_order sc Ex;
        po_sc    : inclusion _ po sc;
        rf_val   : rf_valid rf;
        rf_wf    : reads_from_wf rf;
        rf_sc    : reads_from_sc rf sc rf_val;
        (* no_mix   : exists sz, forall e1, e1 \in Ex -> *)
        (*                         match loc e1 with *)
        (*                         | Some (_, ofs, sz') => *)
        (*                           sz = sz' *)
        (*                         | None => True *)
        (*                         end *)
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
        
