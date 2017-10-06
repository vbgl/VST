(** * Relations library utilities *)

Require Import Coq.Sets.Ensembles.
Require Import concurrency.Ensembles_util.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Sets.Finite_sets.
Require Import Coq.Sets.Finite_sets_facts.

Definition restr {A:Type} (R:relation A) (U: Ensemble A) : relation A :=
  fun x y => R x y /\ x \in U /\ y \in U.
          
Notation "R ?" := (fun x y => R x y \/ x = y) (at level 40).

Module Order.

  Record strict_partial_order {A:Type} (R: relation A) :=
    { antisym : antisymmetric _ R;
      trans   : transitive _ R;
      strict  : forall x : A, ~ R x x
    }.

  Lemma strict_partial_order_antisym {A:Type} {R: relation A}:
    strict_partial_order R -> antisymmetric _ R.
  Proof.
    intro SPO;
      now destruct SPO.
  Qed.

  Lemma strict_partial_order_trans {A:Type} {R: relation A}:
    strict_partial_order R -> transitive _ R.
  Proof.
    intro SPO;
      now destruct SPO.
  Qed.

  Lemma strict_partial_order_strict {A:Type} {R: relation A}:
    strict_partial_order R -> forall x, ~R x x.
  Proof.
    intro SPO;
      now destruct SPO.
  Qed.

  Hint Resolve
       strict_partial_order_antisym strict_partial_order_trans
       strict_partial_order_strict : Relations_db.

  Record strict_total_order {A:Type} (R: relation A) (U: Ensemble A) :=
    { PO : strict_partial_order R;
      total : forall e1 e2 (Hneq: e1 <> e2)
                (Hdom: e1 \in U /\ e2 \in U),
          R e1 e2 \/ R e2 e1;
      R_onto  : forall e1 e2, R e1 e2 -> e1 \in U /\ e2 \in U;
    }.

  Lemma strict_total_order_PO {A:Type} {R: relation A} (U: Ensemble A):
    strict_total_order R U -> strict_partial_order R.
  Proof.
    intro STO;
      now destruct STO.
  Qed.

  Lemma strict_total_order_total {A:Type} {R: relation A} (U: Ensemble A):
    strict_total_order R U ->  forall e1 e2 (Hneq: e1 <> e2)
                                (Hdom: e1 \in U /\ e2 \in U),
      R e1 e2 \/ R e2 e1.
  Proof.
    intro STO;
      now destruct STO.
  Qed.

  Lemma strict_total_order_onto {A:Type} {R: relation A} (U: Ensemble A):
    strict_total_order R U ->
    forall e1 e2, R e1 e2 -> e1 \in U /\ e2 \in U.
  Proof.
    intro STO;
      now destruct STO.
  Qed.

  Hint Resolve
       strict_total_order_total strict_total_order_PO
       strict_total_order_onto : Relations_db.

  (** R-minimal elements in U *)
  Definition min {A:Type} (R: relation A) (U: Ensemble A) : Ensemble A :=
    [ set x | x \in U /\ ~exists y, y \in U /\ R y x ].

End Order.

Module Enumerate.
  Import Order.
  Open Scope Ensembles_scope.
  
  Definition immediate {A:Type} (R: relation A) : relation A :=
    fun x y => R x y /\ ~ exists z, R x z /\ R z y.

  (* Inductive enumerate {A:Type} (R: relation A) : Ensemble A -> list A -> Prop := *)
  (* | EmptySet: enumerate R (Empty_set _) nil *)
  (* | SingletonSet: forall x, enumerate R (Singleton _ x) (x :: nil) *)
  (* | ConsSet: forall x y es es' *)
  (*              (HR: immediate R x y) *)
  (*              (Henum: enumerate R (Union _ es (Singleton _ y)) (y :: es')), *)
  (*     enumerate R (Union _ (Union _ es (Singleton _ y)) (Singleton _ x)) (x :: y :: es'). *)

  (* TODO: move? *)
  Open Scope list.
  Fixpoint In2 {A:Type} (x : A) (y: A) (l : list A) {struct l} :=
    match l with
    | nil => False
    | a :: l' =>
      match l' with
      | nil => False
      | b :: l'' => (a = x /\ b = y) \/ (In2 x y l')
      end
    end.
  Close Scope list.


  (** Enumerate a (finite) set to a list according to the order defined by R *)
  Definition enumerate {A:Type} (R : relation A) (U: Ensemble A) (xs : list A) :=
    (forall x, x \in U <-> List.In x xs) /\
    (forall x y, In2 x y xs -> immediate R x y).

  Lemma enumerate_spec :
    forall {A:Type} R es es' es'' e e'
      (Htrans: transitive A R)
      (Henum: enumerate R es (es' ++ (e::nil) ++ es'')) 
      (HIn: List.In e' es''),
      R e e'.
  Proof.
    intros.
    destruct Henum as [_ HIn2].
    clear es.
    generalize dependent es''.
    generalize dependent e.
    generalize dependent e'.
    induction es'; intros.
    - destruct es''; [simpl in HIn; now exfalso|].
      simpl in HIn.
      destruct HIn; subst.
      eapply HIn2.
      simpl;
        now auto.
      generalize dependent a.
      generalize dependent e.
      generalize dependent e'.
      induction es''; intros.
      + simpl in H; now exfalso.
      + simpl in H.
        destruct H; subst.
        * eapply Htrans;
            eapply HIn2; simpl;
              [left | right];
              now auto.
        * assert (HIn2': forall x y : A, In2 x y (a0 :: (a :: es'')%list) -> immediate R x y).
          { intros.
            eapply HIn2.
            simpl.
            right;
              now eauto.
          }
          pose proof (IHes'' e' H a0 a ltac:(simpl; eauto)).
          eapply Htrans.
          eapply HIn2; simpl; eauto.
          assumption.
    - assert (HIn2': forall x y : A, In2 x y (es' ++ (e :: nil) ++ es'') ->
                                immediate R x y).
      { intros.
        eapply HIn2.
        destruct es'; simpl;
          now eauto.
      }
      eapply IHes';
        now eauto.
  Qed.

  Corollary enumerate_hd:
    forall {A:Type} es R e es' e'
      (Htrans: transitive A R)
      (Henum: enumerate R es (e :: es'))
      (Hin: List.In e' es'),
      R e e'.
  Proof.
    intros.
    apply List.in_split in Hin.
    destruct Hin as [l1 [l2 Heq]].
    subst.
    eapply @enumerate_spec with (es' := nil) (es'' := (l1 ++ e' :: l2)%list) in Henum;
      eauto.
    apply List.in_or_app; simpl;
      now auto.
  Qed.

  Lemma enumerate_hd_ext:
    forall {A:Type} (R: relation A) es esl esl' e e'
      (Hdec: forall n m : A , {n = m} + {n <> m})
      (HPO: strict_partial_order R)
      (Henum: enumerate R es (e :: esl)%list)
      (Henum': enumerate R es (e' :: esl')%list),
      e = e'.
  Proof.
    intros.
    destruct (Hdec e e'); subst; auto.
    pose proof Henum as [HIn HIn2].
    pose proof Henum' as [HIn' HIn2'].
    pose proof (proj2 (HIn e) ltac:(simpl;auto)) as HIne.
    pose proof (proj2 (HIn' e') ltac:(simpl;auto)) as HIne'.
    pose proof (proj1 (HIn' _) HIne) as HIne_es'.
    pose proof (proj1 (HIn _) HIne') as HIne'_es.
    simpl in HIne_es', HIne'_es;
      destruct HIne_es', HIne'_es; auto.
    eapply antisym; eauto.
    eapply @enumerate_spec with (es' := nil) (e' := e') in Henum;
      eauto with Relations_db.
    eapply @enumerate_spec with (es' := nil) (e' := e) in Henum';
      eauto with Relations_db.
  Qed.

  Lemma enumerate_no_dup:
    forall {A:Type} (R:relation A) es e esl
      (HPO: strict_partial_order R)
      (Henum: enumerate R es (e :: esl)),
      ~ List.In e esl.
  Proof.
    intros.
    intros HIn.
    eapply @enumerate_spec with (es' := nil) (e:= e) in HIn;
      eauto with Relations_db.
    eapply strict;
      eauto with Relations_db.
  Qed.

  Lemma enumerate_minus:
    forall {A:Type} (R:relation A) es e esl
      (HPO: strict_partial_order R)
      (Henum: enumerate R es (e :: esl)),
      enumerate R (Setminus _ es (Singleton _ e)) esl.
  Proof.
    intros.
    inversion Henum.
    split.
    - intros e'.
      split.
      + intros HIn.
        inversion HIn.
        pose proof (proj1 (H e') H1) as HInList.
        simpl in HInList.
        destruct HInList; subst; auto.
        exfalso.
        apply H2;
          now auto.
      + intros HIn.
        pose proof (proj2 (H e') ltac:(simpl; eauto)) as HInSet.
        constructor; eauto.
        intros Hcontra.
        inv Hcontra.
        eapply enumerate_no_dup;
          now eauto.
    - intros e1 e2.
      intros HIn2.
      destruct esl.
      inversion HIn2.
      eapply H0.
      simpl;
        now auto.
  Qed.

  Lemma enumerate_ext:
    forall {A:Type} {R: relation A}
      es esl esl'
      (Hdec: forall n m : A, {n=m} + {n<>m})
      (HPO: strict_partial_order R)
      (Henum: enumerate R es esl)
      (Henum': enumerate R es esl'),
      esl = esl'.
  Proof.
    intros ? ? es esl.
    generalize dependent es.
    induction esl.
    - intros.
      destruct Henum as [Hempty _].
      destruct esl' as [|a esl']; [reflexivity|].
      destruct Henum' as [Henum' _].
      pose proof (proj2 (Henum' a) ltac:(simpl;eauto)) as HIn.
      pose proof (proj1 (Hempty a) HIn) as Hcontra.
      simpl in Hcontra.
      now exfalso.
    - intros.
      destruct esl'.
      + destruct Henum as [HIn _].
        destruct Henum' as [HIn' _].
        exfalso.
        pose proof (proj2 (HIn a) ltac:(simpl; auto)) as Ha.
        apply HIn' in Ha.
        now inversion Ha.
      + pose proof (enumerate_hd_ext _ _ _ _ _ _ Hdec HPO Henum Henum').
        subst.
        eapply enumerate_minus in Henum; eauto.
        eapply enumerate_minus in Henum'; eauto.
        apply f_equal.
        now eauto.
  Qed.

Inductive rn {A:Type} (R:relation A): nat -> A -> A -> Prop :=
  | R0: forall x, rn R 0 x x
  | Rn: forall n x y z
          (Hr: immediate R x y)
          (HrN: rn R n y z),
      rn R (S n) x z.

  Lemma R_equiv_Rn:
    forall {A:Type} (R:relation A) (U : Ensemble A) (Hfin: Finite _ U)
      x y
      (HPO: strict_partial_order R)
      (Honto: forall a b, R a b -> a \in U /\ b \in U),
      R x y <-> exists n, rn R (S n) x y.
  Proof.
    Admitted.
    (* intros. *)
    (* split. *)
    (* - intro Hr. *)
    (*   remember (fun a => a \in U /\ R x a /\ (R? a y)) as Bx. *)
    (*   assert (HfinX: Finite _ Bx). *)
    (*   { eapply Finite_downward_closed with (A := U); eauto. *)
    (*     intros a0 HIn0. *)
    (*     subst. *)
    (*     inversion HIn0; *)
    (*       now eauto with Ensembles_DB. *)
    (*   } *)
    (*   generalize dependent x. *)
    (*   apply finite_cardinal in HfinX. *)
    (*   destruct HfinX as (n & HfinX). *)
    (*   generalize dependent Bx. *)
    (*   induction n; intros. *)
    (*   + admit. *)
    (*   + Lemma bla: *)
    (*       forall {A:Type} (R:Relation A) (U: Ensemble A) n *)
    (*         (Hfin: cardinal _ U n) *)
    (*         (Honto: forall a b, R a b -> a \in U /\ b \in U) *)
    (*         x y *)
    (*         (Hr: R x y) *)
    (*         (HPO: strict_partial_order R), *)
    (*       exists x0, x0 \in Order.min R (fun a => In _ U a /\ R x a /\ (R? a y)). *)
    (*     Proof. *)
    (*       intros A R U n. *)
    (*       generalize dependent R. *)
    (*       generalize dependent U. *)
    (*       induction n; intros. *)
    (*       - inversion Hfin. *)
    (*         apply Honto in Hr. *)
    (*         rewrite <- H in Hr. *)
    (*         destruct Hr as [Hcontra _]. *)
    (*         now inversion Hcontra. *)
    (*       - inversion Hfin as[|U0 m Hfin0 x0 Hfresh0]; subst. *)
    (*         destruct (Honto _ _ Hr) as [Hx Hy]. *)
            
    (*         destruct (IHn U0 (restr R U0) Hfin0 ltac:(assert(False) by admit; now exfalso) _ _ Hr HPO). *)
    (*         rewrite H. *)
            
    (*         ar *)


    (*           generalize dependent x. *)
    (*         generalize dependent Bx. *)
    (*         generalize dependent U. *)
    (*         eapply set_ind with (U := U'); eauto. *)
    (*       - intros. *)
    (*         inv HyInU'. *)
    (*       - intros a U Hfresh Hfini IH U0 Hfin0 x y Hsub Hiny Honto Hclosed Hr. *)


    (*         Lemma R_equiv_Rn: *)
    (*           forall {A:Type} (R:relation A) (U U': Ensemble A) (Hfin: Finite _ U) *)
    (*             x y *)
    (*             (Hsub: U' \subset U) *)
    (*             (HyInU': y \in U') *)
    (*             (Honto: forall a b, R a b -> a \in U /\ b \in U) *)
    (*             (Hclosed: forall a b, R a b -> b \in U' -> a \in U'), *)
    (*             R x y -> exists n, rn R n x y. *)
    (*         Proof. *)
    (*           intros A R U U'. *)
    (*           generalize dependent U. *)
    (*           eapply set_ind with (U := U'); eauto. *)
    (*           - intros. *)
    (*             inv HyInU'. *)
    (*           - intros a U Hfresh Hfini IH U0 Hfin0 x y Hsub Hiny Honto Hclosed Hr. *)


    (*             + intros ? ? R Honto Hclosed x y HyInU' Hr. *)
    (*               exfalso. *)
    (*               destruct (Honto _ _ Hr) as [Hcontra _]; *)
    (*                 now inv Hcontra. *)
    (*             + intros a U0 Hfresh Hfin0 IH U' Hsub R Honto Hclosed x y HyInU' Hr. *)
                  



    (*               (* intros A R U U' Hfin. *) *)
    (*               (* intros. *) *)
    (*               (* split. *) *)
    (*               (* - generalize dependent y. *) *)
    (*               (*   generalize dependent x. *) *)
    (*               (*   generalize dependent R. *) *)
    (*               (*   generalize dependent U'. *) *)
    (*               (*   eapply set_ind with (U := U); eauto. *) *)
    (*               (*   + intros ? ? R Honto Hclosed x y HyInU' Hr. *) *)
    (*               (*     exfalso. *) *)
    (*               (*     destruct (Honto _ _ Hr) as [Hcontra _]; *) *)
    (*               (*       now inv Hcontra. *) *)
    (*               (*   + intros a U0 Hfresh Hfin0 IH U' Hsub R Honto Hclosed x y HyInU' Hr. *) *)
                  
    (*               (*     destruct (Honto _ _ Hr) as [Hx Hy]. *) *)
    (*               (*     eapply Add_inv in Hx. *) *)
    (*               (*     eapply Add_inv in Hy. *) *)
    (*               (*     destruct Hx as [Hx | ?], Hy as [Hy |?]; subst. *) *)
    (*               (*     * (** Case x \in U0, y \in U0 *) *) *)

    (*               (*       Definition restr {A:Type} (R:relation A) (U: Ensemble A) : relation A := *) *)
    (*               (*         fun x y => R x y /\ x \in U /\ y \in U. *) *)

    (*               (*       assert (Honto': forall a b, (restr R U0) a b -> In _ U0 a /\ In _ U0 b) *) *)
    (*               (*         by (intros ? ? HresR; *) *)
    (*               (*             destruct HresR; *) *)
    (*               (*             now auto). *) *)
    (*               (*       assert (Hclosed': forall a b : A, (restr R U0) a b -> In A U' b -> In A U' a). *) *)
    (*               (*       { intros a0 b0 HRrestr HInb0. *) *)
    (*               (*         destruct HRrestr. *) *)
    (*               (*         eapply Hclosed; *) *)
    (*               (*           now eauto. *) *)
    (*               (*       } *) *)
    (*               (*       destruct (IH (restr R U0) Honto' Hclosed' x y) as (n & Hrn); auto. *) *)
    (*               (*       split; now auto. *) *)
    (*               (*       exists n. *) *)

    (*               Lemma rn_restr: *)
    (*                 forall {A:Type} {R:Relation A} *)
    (*                   n x y U U' *)
    (*                   (Hincl: U' \subset U) *)
    (*                   (Hclosed: forall a b, R a b -> b \in U' -> a \in U') *)
    (*                   (* (Honto: forall a b, R a b -> a \in U /\ b \in U) *) *)
    (*                   (Hy: y \in U') *)
    (*                   (Hrn: rn (restr R U) n x y), *)
    (*                   rn R n x y. *)
    (*               Proof. *)
    (*                 induction n; intros. *)
    (*                 - inv Hrn. *)
    (*                   now constructor. *)
    (*                 - inv Hrn. *)
    (*                   destruct Hr as [Hr Himm]. *)
    (*                   econstructor; eauto. *)
    (*                   destruct Hr as (Hr & Hin & Hin'). *)
    (*                   split; eauto. *)
    (*                   intros Hcontra. *)
    (*                   apply Himm. *)
    (*                   destruct Hcontra as (z & Hrxz & Hrzy). *)
    (*                   assert (HRy0y: R y0 y) by admit. *)
    (*                   eapply Hclosed in HRy0y; eauto. *)
    (*                   exists z; *)
    (*                     repeat (split; eauto). *)
    (*               Admitted. *)
                  
                  
  (* eapply @rn_restr with (U := U0); eauto. *)

End Enumerate.
