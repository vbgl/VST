(** * Relations library utilities *)

Require Import Coq.Sets.Ensembles.
Require Import concurrency.Ensembles_util.
Require Import Coq.Relations.Relation_Definitions.

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

 

End Enumerate.