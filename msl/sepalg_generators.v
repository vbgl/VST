(*
 * Copyright (c) 2009-2011, Andrew Appel, Robert Dockins and Aquinas Hobor.
 *
 *)

(** This module defines the standard operators on separation algebras, including
    the operators over pairs, disjoint sums, function spaces, dependent products,
    dependent sums, sub-separation algebras, the discrete separation algebra,
    the trivial unit and void separation algrbras.
*)

Require Import msl.base.
Require Import msl.sepalg.

(** The trivial separation algebra over the unit type.  This SA
    is the identity of the product SA operator, up to isomorphism.
*)

  Instance Join_unit : Join unit := fun x y z => True.

  Instance Perm_unit : Perm_alg unit.
  Proof.
  constructor; auto with typeclass_instances; try firstorder.
  destruct z; destruct z'; auto.
  destruct a; destruct b; auto.
  Qed.

  Instance Sep_unit: Sep_alg unit.
  Proof. apply mkSep with (fun _ => tt); intros;  hnf; auto with typeclass_instances. Qed.

  Instance Core_unit: Core_alg unit.
  Proof. apply mkCore with Sep_unit; intros;  hnf; auto.
         destruct a, (core tt); auto.
  Qed.
  
  Instance Sing_unit: Sing_alg unit.
  Proof. apply (mkSing tt); intros; hnf; simpl.
        destruct (core a); destruct tt; auto.
 Qed.

  Instance Unit_unit: Unital unit.
  Proof. apply (mkUnital unit _ tt); intros; constructor. Qed.
  Instance PUnit_unit: PartialUnital unit.
  Proof.
    apply mkPUnital with (fun _ => tt); intro.
    constructor.
    destruct a0, b; reflexivity.
  Qed.
  
  Instance Canc_unit: Canc_alg unit.
  Proof. repeat intro. auto. hnf; destruct a1; destruct a2; auto. Qed.

  Instance Disj_unit: Disj_alg unit.
  Proof. repeat intro. hnf; destruct a; destruct b;  auto. Qed.

  Instance Cross_unit: Cross_alg unit.
  Proof. repeat intro. exists (tt,tt,tt,tt). repeat split; constructor. Qed.

(** The trivial separation algebra over the void type. This SA
    is the identity of the coproduct (disjoint sum) SA operator, up to isomorphism.
*)

  Inductive Void : Type :=.

  Instance Join_void : Join Void := fun x y z => False.

  Instance Perm_void : Perm_alg Void.
  Proof. constructor; intuition.  Qed.
  Instance Sep_void: Sep_alg Void.
  Proof. apply mkSep with (fun x => x); intros. 
      auto with typeclass_instances. destruct t. destruct a.
  Qed.
  Instance Core_void: Core_alg Void.
  Proof. apply mkCore with Sep_void; intros; destruct a. Qed.
  Instance PUnit_void: PartialUnital Void.
  Proof. apply mkPUnital with (fun x => x); destruct a. Qed.
  Instance Canc_void: Canc_alg Void.
  Proof. repeat intro. destruct b. Qed. 
  Instance Disj_void: Disj_alg Void.
  Proof. repeat intro. destruct a. Qed.
  Instance Cross_void: Cross_alg Void.
  Proof. repeat intro. destruct z. Qed.

(** The separation algebra over booleans, e.g. Z/2 with bounded addition *)

  Inductive join_bool : bool -> bool -> bool -> Prop :=
  | jb_fff: join_bool false false false
  | jb_tft: join_bool true false true
  | jb_ftt: join_bool false true true.

  Instance Join_bool : Join bool := join_bool.

  Instance Perm_bool: Perm_alg bool.
  Proof.
    constructor.
    constructor.
    auto with typeclass_instances.
    intros; inv H; inv H0; hnf; auto.
    repeat intro; hnf in *; subst; auto.
    intros. icase a; icase b; icase d; try solve [elimtype False; (inv H || inv H0)].
    exists c; inv H0; split; constructor.
    exists true; inv H0; split; constructor.
    exists c; inv H0; split; constructor.
    intros; inv H; constructor; auto.
    intros. inv H; inv H0; hnf; auto.
  Qed.

  Instance Sep_bool: Sep_alg bool.
  Proof. apply mkSep with (fun t => false); intros; hnf; auto with typeclass_instances.
     icase t; constructor.
  Defined.
  Instance Core_bool: Core_alg bool.
  Proof. apply mkCore with Sep_bool; intros.
         inv H. reflexivity.
         destruct c; unfold core, Sep_bool in H;
         inv H; auto; constructor.
  Defined.
  Instance Sing_bool: Sing_alg bool.
  Proof. apply (mkSing false). intros; simpl; reflexivity.
  Defined.
  Instance Unit_bool: Unital bool.
  Proof. apply (mkUnital _ _ false); intros; destruct a; constructor. Qed.
  Instance PUnit_bool: PartialUnital bool.
  Proof. eapply Unital_PUnital; auto.
         destruct Perm_bool; auto.
         exact Unit_bool. Qed.
  Instance Canc_bool: Canc_alg bool.
  Proof. repeat intro. inv H; inv H0; hnf; auto. Qed.

  Instance Disj_bool: Disj_alg bool.
  Proof. repeat intro. inv H; hnf; auto. Qed.

  Instance Cross_bool: Cross_alg bool.
  Proof. repeat intro.
     icase a; icase b; try solve [elimtype False; (try inv H; inv H0)];
    icase z; icase c; icase d; try solve [elimtype False; (try inv H; inv H0)].
     exists (true,false,false,false); repeat split; constructor.
     exists (false,true,false,false); repeat split; constructor.
     exists (false,false,true,false); repeat split; constructor.
     exists (false,false,false,true); repeat split; constructor.
     exists (false,false,false,false); repeat split; constructor.
  Qed.     

Section JOIN_EQUIV.
(** The "equivalance" or discrete SA.  In this SA, every element of an arbitrary
    set is made an idempotent element.  We do not add this as a global
    Instance, because it is too widely applicable in cases where we do not
    desire it.
*)

  Instance Join_equiv (A: Type) : Join A := fun x y z => x=y/\y=z.

  Instance Perm_equiv (A: Type) :  @Perm_alg A (Join_equiv A).
  Proof. constructor; intros.
     constructor; intros.
     destruct H; destruct H0; unfold equiv in *; subst; auto.
     destruct H; destruct H0; subst. exists e; split; split; auto.
     destruct H; split; subst; auto.
     destruct H; subst; reflexivity.
  Qed.

  Instance Sep_equiv (A: Type): Sep_alg A.
  Proof. apply mkSep with (fun a => a); intros.
            apply Perm_equiv.
            split; reflexivity.
            destruct H; subst; reflexivity.
  Defined.
  Instance Core_equiv (A: Type): Core_alg A.
  Proof. apply mkCore with (Sep_equiv A); intros.
         unfold core, Sep_equiv; reflexivity.
         constructor; reflexivity.
  Defined.
  Instance PUnit_equiv (A: Type): PartialUnital A.
  Proof. apply mkPUnital with (fun x => x); intro s.
         split; reflexivity.
         intros b c HH. inv HH; reflexivity.
  Qed.
  Instance Canc_equiv (A: Type): Canc_alg A.
  Proof. repeat intro. destruct H; destruct H0; subst; reflexivity. Qed.

  Instance Disj_equiv (A: Type): Disj_alg A.
  Proof. repeat intro. destruct H; subst; reflexivity. Qed.

  Instance Cross_equiv (A: Type): Cross_alg A.
  Proof. repeat intro. destruct H; destruct H0; subst.
   exists (z,z,z,z); repeat split; reflexivity.
  Qed.

Lemma join_equiv_refl: forall A (v: A), @join A (Join_equiv A) v v v.
Proof. split; auto. Qed.
End JOIN_EQUIV.

(* WARNING: DO NOT DO    [EXisting Instance Join_equiv]   BECAUSE
   IT WILL MATCH IN UNINTENDED PLACES.  But I think it will do no harm
  to do the following EXisting Instances: *)
Existing Instance Perm_equiv.
Existing Instance Sep_equiv.
Existing Instance Core_equiv.
Existing Instance PUnit_equiv.
Existing Instance Canc_equiv.
Existing Instance Disj_equiv.
Existing Instance Cross_equiv.

Hint Extern 1 (@join _ _ _ _ _) => 
   match goal with |- @join _ (@Join_equiv _) _ _ _ => apply join_equiv_refl end.
(* Hint Resolve @join_equiv_refl. *)

Section SepAlgProp.
  Variable A:Type.
  Variable JOIN: Join A.
  Variable PA: Perm_alg A.
  Variable P:A -> Prop.

  Variable HPjoin : forall x y z, join x y z -> P x -> P y -> P z.

  Instance Join_prop : Join (sig P) := 
                 fun x y z: (sig P) => join (proj1_sig x) (proj1_sig y) (proj1_sig z).    

  Instance Perm_prop : Perm_alg (sig P).
  Proof.
   constructor; intros.
   constructor; intros.
    destruct z; destruct z'. apply exist_ext. do 2 red in H,H0; eapply join_eq; eauto.
    do 2 red in H,H0.
    destruct (join_assoc H H0) as [f [? ?]].
     assert (P f) by (apply (HPjoin _ _ _ H1); auto; apply proj2_sig; auto).
     exists (exist P f H3).
     split; auto.
     do 2 red in H; apply join_comm in H; auto.
     do 2 red in H,H0. simpl in H,H0.
     destruct a, b; simpl; apply exist_ext; eapply join_positivity; eauto.
 Qed.

  Instance Sep_prop (SA: Sep_alg A)(HPcore : forall x, P x -> P (core x)): Sep_alg (sig P).
  Proof. repeat intro.
     apply mkSep with (fun a : sig P => exist P (core (proj1_sig a)) (HPcore _ (proj2_sig a)));
      intros. apply Perm_prop.
      do 2 red. destruct t; simpl. apply join_comm; apply core_unit.
      apply exist_ext.
      do 2 red in H. apply join_core in H. apply H.
  Defined.
  Instance Core_prop (CA: Core_alg A)(HPcore : forall x, P x -> P (core x)): Core_alg (sig P).
  Proof. repeat intro.
         apply mkCore with (Sep_prop CA HPcore); intros.
         destruct a as [a ?];
         apply exist_ext; apply dup_core; apply H.
         destruct a, b, c; do 2 red in H; simpl in H.
         apply split_core in H. exact H.
  Defined.
 Instance Sing_prop  (SA: Sep_alg A)(Sing_A: Sing_alg A)
               (HPcore : forall x, P x -> P (core x)): P the_unit -> 
    @Sing_alg (sig P) Join_prop (Sep_prop _ HPcore).
 Proof. intros.
  apply (mkSing (exist P the_unit H)).
  intros. destruct a as  [a Ha]. simpl. apply exist_ext.
  rewrite <- (the_unit_core a).
  apply core_uniq.
 Defined.

 Instance Unit_prop  (UA: Unital A)(Unit: P join_unit):  Unital (sig P).
 Proof.
   apply mkUnital with (exist P join_unit Unit). intros [a Ha].
   unfold join, Join_prop; simpl.
   apply join_lid.
 Qed.
 
 Instance PUnit_prop (PU: PartialUnital A)(HPpunit : forall x, P x -> P (punit x)): PartialUnital (sig P).
 Proof. repeat intro.
        apply mkPUnital with
        (fun a : sig P => exist P (punit (proj1_sig a)) (HPpunit _ (proj2_sig a)));
          intros a. apply Perm_prop.
        do 2 red. destruct a; simpl. apply join_comm; apply punit_unit.
        intros b c HH.
        destruct a, b, c. simpl in *.
        apply exist_ext.
        eapply join_punit with x; exact HH.
 Defined.

  Instance Canc_prop  {CA: Canc_alg A}:  Canc_alg (sig P).
  Proof.
   intros [a Ha] [b Hb] [c1 Hc1] [c2 Hc2].
    unfold join, Join_prop; simpl; intros. apply exist_ext.
  eapply join_canc; eauto.
  Qed.

  Instance Disj_prop {DA: Disj_alg A}: Disj_alg (sig P).
  Proof. intros [a Ha][b Hb].
    unfold join, Join_prop; simpl; intros.
    apply exist_ext. apply join_self; auto.
  Qed.

(*  Instance CS_prop {CS: Cross_alg A}: Cross_alg (sig P). ... not true ...
  Proof. intros [a Ha][b Hb][c Hc][d Hd][z Hz].
    unfold join, Join_prop, equiv, Equiv_prop; simpl; intros.
   destruct (cross_split _ _ _ _ _ H H0) as [[[[ac ad] bc] bd][? [? [? ?]]]].
*)

End SepAlgProp.
Existing Instance Join_prop.
Existing Instance Perm_prop.
Existing Instance Core_prop.
Existing Instance Sep_prop.
Existing Instance Sing_prop.
Existing Instance Unit_prop.
Existing Instance Canc_prop.
Existing Instance Disj_prop.

(** The function space operator from a key type [key] to
    a separation algebra on type [t'].
*)
Section SepAlgFun.
  Variable key: Type.
  Variable t' : Type.
  Variable JOIN: Join t'.
  Variable Pt': Perm_alg t'.

  Instance Join_fun: Join (key -> t') := 
                  fun a b c : key -> t' => forall x, join (a x) (b x) (c x).

  Instance Perm_fun : Perm_alg (key -> t').
  Proof.
   constructor; intros.
   constructor; intros.
   extensionality k.
   apply (join_eq (H k) (H0 k)).
  exists (fun x => projT1 (join_assoc (H x) (H0 x))).
  split; intro k; destruct (join_assoc (H k) (H0 k)) as [f [? ?]]; auto.
  intro k; apply join_comm; apply H.
  extensionality k; specialize (H k); specialize (H0 k).
  apply (join_positivity H H0).
 Qed.

  Instance Sep_fun (SA: Sep_alg t'): Sep_alg (key -> t').
  Proof. apply mkSep with (fun a k => core (a k)); intros.
   intro k; apply core_unit.
   extensionality k; apply @join_core with (b k); auto.
 Defined.

  Instance Core_fun (SA: Core_alg t'): Core_alg (key -> t').
  Proof.
    apply mkCore with (Sep_fun SA); intros.
    extensionality k.
    unfold core, Sep_fun; simpl.
    apply dup_core.
    apply H.
    intros k. apply (split_core _ _ _ (H k)).
  Defined.
 Instance Sing_fun (SA: Sep_alg t'): Sing_alg t' -> Sing_alg (key -> t').
 Proof.
 intros. apply (mkSing (fun _: key => the_unit)).
 intro a; extensionality k.
 rewrite <- (the_unit_core (a k)). 
  unfold core. simpl. auto.
 Defined. 

 Instance Unit_fun: Unital t' -> Unital (key -> t').
 intros. apply mkUnital with (fun _ => join_unit); intros.
 unfold join, Join_fun; intros k; apply join_lid.
 Defined.
  
 Instance PUnit_fun: PartialUnital t' -> PartialUnital (key -> t').
 intros PU.
 apply mkPUnital with (fun a k => punit (a k)); intros.
 unfold join, Join_fun; intros HH.
 apply punit_unit.
 
 intros b c HH.
 extensionality x; specialize (HH x).
 apply (join_punit (a x) ).
 assumption.
 Defined.
 

  Instance Canc_fun: Canc_alg t' -> Canc_alg (key -> t').
 Proof. repeat intro. extensionality x; apply (join_canc (H0 x) (H1 x)). Qed.

 Instance Disj_fun: Disj_alg t' -> Disj_alg (key -> t').
 Proof.  repeat intro. extensionality x;  apply H. apply H0. Qed.
End SepAlgFun.

Existing Instance Join_fun. 
Existing Instance Perm_fun.
Existing Instance Sep_fun.
Existing Instance Core_fun.
Existing Instance Sing_fun.
Existing Instance Unit_fun.
Existing Instance PUnit_fun.
Existing Instance Canc_fun.
Existing Instance Disj_fun.

(** The dependent product SA operator from an index set [I] into
    a SA indexed by [Pi_j].  The construction of this
    operator either requires constructive witnesses for the unit
    and associativity axioms or some form of the axiom of choice.
    We have chosen to have explicitly constructive witnesses
    and avoid the use of choice.
*)

Section SepAlgPi.
  Variable I:Type.  
  Variable Pi: I -> Type.
  Variable pi_J: forall i, Join (Pi i).
  Variable PA:  forall i, Perm_alg (Pi i).

  Let P := forall i:I, Pi i.

  Instance Join_pi: Join P := fun x y z => forall i:I, join (x i) (y i) (z i).

  Instance Perm_pi  : Perm_alg P.
  Proof.
   constructor; intros.
   constructor; intros.
   extensionality i. apply (join_eq (H i) (H0 i)).
   exists (fun i => projT1 (join_assoc (H i) (H0 i))).
   split; intro i; destruct (join_assoc (H i) (H0 i)) as [f [? ?]]; auto.
   intro i; apply join_comm; auto.
   extensionality i. specialize (H i); specialize (H0 i).
   apply (join_positivity H H0).
 Qed.

  Instance Sep_pi (SA : forall i:I, Sep_alg (Pi i)): Sep_alg P.
  Proof. apply mkSep with (fun a i => core (a i)); intros.
   intro i; apply core_unit.
   extensionality i; apply @join_core with (b i); auto.
 Defined.

  Instance Core_pi (SA : forall i:I, Core_alg (Pi i)): Core_alg P.
  Proof. apply mkCore with (Sep_pi SA); intros.
         unfold core, Sep_pi.
         extensionality x.
         apply dup_core; apply H.
         intros i.
         apply (split_core _ _ _ (H i)).
  Defined.
         
  Instance Unit_pi: (forall i, Unital (Pi i)) -> Unital P.
  Proof.
    intros. unfold P.
    assert (H: forall i, {x: Pi i | forall a : Pi i, join x a a}).
    intros i. destruct (X i) . apply (@exist _ _ join_unit join_lid).
    apply mkUnital with (fun i => proj1_sig (H i)). intros a.
    unfold join, Join_pi; intros i.
    destruct (H i); simpl. exact (j (a i)).
  Qed.

  Instance PUnit_pi: (forall i, PartialUnital (Pi i)) -> PartialUnital P.
  Proof.
    intros PU.
    apply mkPUnital with (fun a i => punit (a i)); intro ai.
    unfold join, Join_pi; intros.
    apply (punit_unit).

    intros b c.
    unfold join, Join_pi; intros HH.
    extensionality i.
    specialize (HH i).
    apply (@join_punit _ _ (PU i) (ai i)); assumption.
  Qed. 
  
  Instance Canc_pi: (forall i, Canc_alg (Pi i)) -> Canc_alg P.
  Proof. repeat intro. extensionality i; apply (join_canc (H0 i) (H1 i)). Qed.

  Instance Disj_pi: (forall i, Disj_alg (Pi i)) -> Disj_alg P.
  Proof. repeat intro. extensionality i; apply (join_self (H0 i)). Qed.

End SepAlgPi.
Existing Instance Join_pi. 
Existing Instance Perm_pi.
Existing Instance Sep_pi.
Existing Instance Core_pi.
Existing Instance Unit_pi.
Existing Instance PUnit_pi.
Existing Instance Canc_pi.
Existing Instance Disj_pi.

(** The dependent sum operator on SAs.

   Here we have defined the operator under the hypothesis
   that dependent pairs are injective.  This property can
   be proved without axioms provided that 
   the index type [I] enjoys decidable equality.

   The property for all types follows as a corollary of
   Streicher's K axiom (or one of its equivalants).
   The K axiom, in turn, follows from the classical axiom.
   Users who are willing to assume K can then use this
   construction at any index type.

   However, in this version, we use inj_pair2, which comes from
   msl.EXtensionality; the proof there relies on 
   proof-irrelevance (but not on stronger forms of extensionality).
*)
Section SepAlgSigma.
  Variable I:Type.
  Variable Sigma: I -> Type.
  Variable JOIN: forall i, Join (Sigma i).
  Variable PA: forall i, Perm_alg (Sigma i).
  Let S := sigT Sigma.

  Inductive join_sigma : S -> S -> S -> Prop :=
    j_sig_def : forall (i:I) (a b c:Sigma i),
      join a b c ->
      join_sigma (existT Sigma i a) (existT Sigma i b) (existT Sigma i c).
  
  Instance Join_sigma: Join S := join_sigma.

  Instance Perm_sigma: Perm_alg S.
  Proof.  constructor; intros.
   constructor; intros.

    (* join_eq *)
    destruct z as [z Hz]. destruct z' as [z' Hz'].
    destruct x as [x Hx]; destruct y as [y Hy].
    assert (z=z').
    inv H. subst.
    apply inj_pair2 in H3; subst.  apply inj_pair2 in H5; subst.
    apply inj_pair2 in H7; subst.
    inv H0; subst; auto. subst z'.
    f_equal.
    inv H; subst.
   apply inj_pair2 in H3; subst.
    apply inj_pair2 in H5; subst.  apply inj_pair2 in H7;  subst.
    inv H0; subst.
   apply inj_pair2 in H3; subst.
    apply inj_pair2 in H4; subst.  apply inj_pair2 in H5;  subst.
    eapply join_eq; eauto.

    (* join_assoc *)
    destruct a as [ai a]; destruct b as [bi b]; destruct c as [ci c];
    destruct d as [di d]; destruct e as [ei e].
    assert (ai = bi /\ bi = ci /\ ci = di /\ di = ei).
    inv H; inv H0; simpl; auto.
    decompose [and] H1; subst; clear H1.
    rename ei into i.
    assert (join a b d).
    inversion H. apply inj_pair2 in H3. apply inj_pair2 in H4. apply inj_pair2 in H5.
    subst; auto.
    assert (join d c e).
    inversion H0. apply inj_pair2 in H4. apply inj_pair2 in H5. apply inj_pair2 in H6.
    subst; auto.
    destruct (join_assoc H1 H2) as [f [? ?]].
    exists (existT Sigma i f).
    split; constructor; auto.

    (* join_comm *)
    inv H; subst.
    constructor.
    apply join_comm; auto.

    (* join_positivity *)
    inv H; inv H0.  apply inj_pair2 in H3.  apply inj_pair2 in H5.  subst.
    f_equal.
    eapply join_positivity; eauto.
 Qed.



  Instance Sep_sigma (SA : forall i:I, Sep_alg (Sigma i)) : Sep_alg S.
  Proof. apply mkSep with
      (fun (a : S) => existT Sigma (projT1 a) (core (projT2 a))).
   intros [i a]. constructor. apply core_unit.
   intros. inv H. f_equal. apply (join_core H0). 
 Defined.

  Instance Core_sigma (SA : forall i:I, Core_alg (Sigma i)) : Core_alg S.
  Proof. apply mkCore with (Sep_sigma SA); intros.
         destruct a as [a ?].
         simpl; f_equal.
         apply dup_core.
         inversion H.
         apply inj_pair2 in H2;
         apply inj_pair2 in H3;
         apply inj_pair2 in H4.
         subst; auto.

         inv H; constructor.
         apply inj_pair2 in H4.
         rewrite H4 in H3.
         apply (split_core _ _ _ H3).
  Defined.
  
  (* No UNIT:
     If I is empty type, [forall i, Unital (Sigma i)] holds
     vacuously, but [Unital S] doesn't hold because, there is no 
     unit (becasue there is not even a single element). *) 
  (* Instance Unit_sigma: (forall i, Unital (Sigma i)) -> Unital S.*)
  
  
  Instance PUnit_sigma: (forall i, PartialUnital (Sigma i)) -> PartialUnital S.
  Proof.
    intros PU.
    apply mkPUnital with (fun a => existT Sigma (projT1 a) (punit (projT2 a))); intro a.
    destruct a. constructor.
    apply punit_unit.
    intros b c HH. inv HH.
    f_equal.
    apply join_punit with  (projT2 a).
    apply inj_pair2 in H1; rewrite <- H1; assumption.
  Qed.
    
  Instance Canc_sigma: (forall i, Canc_alg (Sigma i)) -> Canc_alg S.
  Proof. repeat intro.
       destruct a1; destruct a2; destruct b; destruct c; 
       inv H0; inv H1; subst.
     apply inj_pair2 in H5; apply inj_pair2 in H10; apply inj_pair2 in H12;  
     apply inj_pair2 in H4; apply inj_pair2 in H6; apply inj_pair2 in H8;  
     subst.
    f_equal. apply (join_canc H3 H2).
  Qed.

  Instance Disj_sigma: (forall i, Disj_alg (Sigma i)) -> Disj_alg S.
  Proof. repeat intro.
    destruct a as [ia a]; destruct b as [ib b].
  (* Some weird bug in Coq requires this two-stage inversion process *)
    red in H0. generalize H0; intro. inv H1.
     apply inj_pair2 in H7; apply inj_pair2 in H4; apply inj_pair2 in H5;  
     subst. inv H0.
     apply inj_pair2 in H4; apply inj_pair2 in H5; apply inj_pair2 in H6;  
     subst.
    f_equal;  apply (join_self H2).
 Qed.
End SepAlgSigma.

Existing Instance Join_sigma. 
Existing Instance Perm_sigma.
Existing Instance Sep_sigma.
Existing Instance Core_sigma.
(*Existing Instance Unit_sigma.*)
Existing Instance PUnit_sigma.
Existing Instance Canc_sigma.
Existing Instance Disj_sigma.

(** The SA operator on cartesian products. *)
Section SepAlgProd.

  Variables (A: Type) (Ja: Join A).
  Variables (B: Type) (Jb: Join B) .
  Variables (PAa: Perm_alg A)(PAb: Perm_alg B).

  Instance Join_prod : Join (A*B) := 
               fun (x y z:A*B) =>  join (fst x) (fst y) (fst z) /\ join (snd x) (snd y) (snd z).

  Instance Perm_prod  : Perm_alg (A*B).
  Proof.
    constructor.
    
    constructor.

    (* join_eq *)
    intros [? ?] [? ?] [? ?] [? ?] [? ?] [? ?]; simpl in *.
    f_equal; simpl; eapply join_eq; eauto.

    (* join_assoc *)
    intros [? ?] [? ?] [? ?] [? ?] [? ?] [? ?] [? ?]; simpl in *.
    destruct (join_assoc H H1) as [x [? ?]].
    destruct (join_assoc H0 H2) as [y [? ?]].
    exists (x,y); simpl; repeat split; auto.

    (* join_comm *)
    intros [? ?] [? ?] [? ?] [? ?]; repeat split; simpl in *; apply join_comm; auto.

    (* join_positivity *)
    intros [? ?] [? ?] [? ?] [? ?] [? ?] [? ?]; simpl in *.
    f_equal; simpl; eapply join_positivity; eauto.
 Qed.

  Instance Sep_prod (SAa: Sep_alg A) (SAb: Sep_alg B) : Sep_alg (A*B).
  Proof.
    apply mkSep with (fun a => (core (fst a), core (snd a))).
    intros [? ?]; split; apply core_unit; auto.
    intros [? ?] [? ?] [? ?] [? ?]; f_equal; simpl; eapply join_core; eauto.
  Defined.

  Instance Core_prod (CAa: Core_alg A) (CAb: Core_alg B) : Core_alg (A*B).
  Proof.
    apply mkCore with (Sep_prod CAa CAb).
    intros [a b] H; inv H.
    unfold core, Sep_prod; f_equal; apply dup_core; simpl; auto.

    intros [a1 b1] [a2 b2] [a3 b3] H; inv H. constructor.
    apply (split_core _ _ _ H0). 
    apply (split_core _ _ _ H1).
  Defined.
    
  Instance Sing_prod {SAa: Sep_alg A} {SAb: Sep_alg B} {SingA: Sing_alg A}{SingB: Sing_alg B}: Sing_alg (A*B).
  Proof. apply (mkSing  (the_unit, the_unit)).
     intros [? ?].  f_equal; simpl; f_equal; apply the_unit_core.
  Defined.

  Instance Unit_prod {Ua: Unital A} {Ub:  Unital B}: Unital (A*B).
  Proof.
    apply mkUnital with (join_unit, join_unit); intros.
    constructor; simpl; apply join_lid.
  Defined.

  Instance PUnit_prod {Ua: PartialUnital A} {Ub:  PartialUnital B}: PartialUnital (A*B).
  Proof.
    apply mkPUnital with (fun a => (punit (fst a), punit (snd a))); intros a; destruct a; simpl.
    constructor; simpl; apply punit_unit.

    intros aa bb HH. destruct aa, bb; inv HH.
    f_equal.
    apply join_punit with a; auto.
    apply join_punit with b; auto.
  Defined.
  
  Instance Canc_prod {CAa: Canc_alg A} {CAb:  Canc_alg B}: Canc_alg (A*B).
  Proof. intros  [? ?] [? ?] [? ?] [? ?] [? ?] [? ?].
   f_equal; simpl in *; eapply join_canc;eauto.
  Qed. 

  Instance Disj_prod {DAa: Disj_alg A} {DAb:  Disj_alg B}: Disj_alg (A*B).
  Proof. intros  [? ?]  [? ?] [? ?].
   f_equal; simpl in *; eapply join_self;eauto.
  Qed. 

End SepAlgProd.

Implicit Arguments Perm_prod [[A][Ja][B][Jb]]. 
Implicit Arguments Sep_prod [[A][Ja][B][Jb]]. 
Existing Instance Join_prod. 
Existing Instance Perm_prod.
Existing Instance Sep_prod.
Existing Instance Core_prod.
Existing Instance Unit_prod.
Existing Instance PUnit_prod.
Existing Instance Canc_prod.
Existing Instance Disj_prod.

(** The SA operator on disjoint sums. *)
Section SepAlgSum.

  Variables (A: Type) (Ja: Join A) .
  Variables (B: Type) (Jb: Join B) .
  Variables (PAa: Perm_alg A) (PAb: Perm_alg B).
  Instance Join_sum : Join (A+B) := 
    (fun (x y z: A+B) =>
    match x, y, z with
    | inl xa, inl ya, inl za => join xa ya za
    | inr xb, inr yb, inr zb => join xb yb zb
    | _, _, _ => False
    end).

  Instance Perm_sum: Perm_alg (A+B).
  Proof.
    constructor.
    constructor.

    intros. icase x; icase y; icase z; icase z'; simpl in *; hnf; simpl;
    f_equal; eapply join_eq; eauto.

    (* join_assoc *)
    intros; destruct e,a,b,c,d; try contradiction; hnf in H,H0;
    destruct (join_assoc H H0) as [f [? ?]].
    exists (inl B f); simpl; auto.
    exists (inr A f); simpl; auto.

    (* join_comm *)
    intros; destruct a; destruct b; destruct c; hnf in H|-*; try contradiction;
    apply join_comm; auto.

    (* join_positivity *) 
    intros; hnf in H,H0|-*; destruct a; destruct a'; destruct b; destruct b'; try contradiction;
    f_equal; eapply join_positivity; eauto.
 Qed.

  Instance Sep_sum (SAa: Sep_alg A) (SAb: Sep_alg B): Sep_alg (A+B).
  Proof.
    apply mkSep 
      with (fun ab : A+B => 
              match ab with 
              | inl a => inl _ (core a) 
              | inr b => inr _ (core b)
              end).
    intro a; icase a; hnf; apply core_unit; auto.
    intros; icase a; icase b; icase c; hnf in *; f_equal; eapply join_core; eauto.
  Defined.

  Instance Core_sum (CAa: Core_alg A) (CAb: Core_alg B): Core_alg (A+B).
  Proof.
    apply mkCore with (Sep_sum CAa CAb).
    intros [a| b] H; simpl; f_equal; apply dup_core; auto.
    intros [a| a] [b| b] [c| c] HH; simpl in HH;
    unfold join, Join_sum in HH; try solve[inv HH];
    unfold join, Join_sum; eapply split_core; eauto.
  Qed.
    
  (*No UNIT: A's and B's don't mix so a unit can't be either type -> no unit*)
  (*Instance Unit_sum {Ua: Unital A} {Ub:  Unital B}: Unital (A+B). *)
  
  Instance PUnit_sum {Ua: PartialUnital A} {Ub:  PartialUnital B}: PartialUnital (A+B).
  Proof.
    apply mkPUnital
      with (fun ab : A+B => 
              match ab with 
              | inl a => inl _ (punit a) 
              | inr b => inr _ (punit b)
              end); intros a; destruct a.
    apply punit_unit.
    apply punit_unit.
    intros b c HH. destruct b, c; try inv HH.
    f_equal; apply join_punit with a; auto.
    intros a c HH. destruct a, c; try inv HH.
    f_equal; apply join_punit with b; auto.
  Qed.
      
  Instance Canc_sum {CAa: Canc_alg A} {CAb:  Canc_alg B}: Canc_alg (A+B).
  Proof. repeat intro. icase a1; icase a2; icase b; icase c; hnf;
    f_equal; eapply join_canc; hnf in *; eauto.
  Qed. 

  Instance Disj_sum {DAa: Disj_alg A} {DAb:  Disj_alg B}: Disj_alg (A+B).
  Proof. repeat intro.  hnf in H|-*; icase a; icase b; simpl; f_equal; eapply join_self;eauto.
  Qed.

End SepAlgSum.
Existing Instance Join_sum. 
Existing Instance Perm_sum.
Existing Instance Sep_sum.
Existing Instance Core_sum.
(*Existing Instance Unit_sum.*)
Existing Instance PUnit_sum.
Existing Instance Canc_sum.
Existing Instance Disj_sum.

(** The SA operator on lists.  Lists are joined componentwise.
 *)
Section sa_list.

  Variables (A: Type) (Ja: Join A)  (PAa: Perm_alg A).

  Inductive list_join : list A -> list A -> list A -> Prop :=
  | lj_nil : list_join nil nil nil
  | lj_cons : forall x y z xs ys zs,
      join x y z ->
      list_join xs ys zs ->
      list_join (x::xs) (y::ys) (z::zs).

  Instance Join_list: Join (list A) := list_join.

  Instance Perm_list: Perm_alg (list A).
  Proof.
    constructor.
    constructor.

    induction x; intros; inv H; inv H0; auto; try constructor.
    f_equal. eapply join_eq; eauto. eapply IHx; eauto.

    induction a; intros; 
    destruct b; destruct d; try (elimtype False; inv H; fail);
    destruct c; destruct e; try (elimtype False; inv H0; fail).
    exists nil. split; constructor.
    assert (join a a1 a2) by (inv H; auto).
    assert (join a2 a3 a4) by (inv H0; auto).
    assert (list_join a0 b d) by (inv H; auto).
    assert (list_join d c e) by (inv H0; auto).
    destruct (join_assoc H1 H2) as [z [? ?]].
    destruct (IHa _ _ _ _ H3 H4) as [zs [? ?]].
    exists (z::zs); split; constructor; auto.
    induction a; intros; inv H; constructor; auto.
    apply IHa; auto.
    
    induction a; intros.
    inv H; inv H0; auto.
    inv H0; inv H.
    f_equal.  eapply join_positivity; eauto. 
    eapply IHa; eauto.
 Qed.

  Instance Sep_list (SAa: Sep_alg A) : Sep_alg (list A).
  Proof.
    apply mkSep with (map core).
    induction t; constructor; auto; apply core_unit.
    induction a; intros; inv H; auto. simpl. 
    f_equal.  eapply join_core; eauto. eapply IHa; eauto.
 Defined.

  
  Instance Core_list (CAa: Core_alg A) : Core_alg (list A).
  Proof.
    apply mkCore with (Sep_list CAa).
    induction a. simpl; auto.
    intros HH; inv HH; simpl.
    f_equal; auto.
    apply dup_core; auto.

    induction a. simpl; auto. constructor.
    intros b c HH; inv HH.
    constructor.
    destruct c; inv H1.
    eapply (split_core _ _ _ H3); auto.
   
    destruct c; inv H1.
    apply (IHa _ _ H4).
  Qed.
    
    (*No UNIT: lists are same length -> no universal unit*)
  (*Instance Unit_list {UA: Unital A}: Unital (list A).*)


  Instance PUnit_list {PUA: PartialUnital A}: PartialUnital (list A).
  Proof.
    apply mkPUnital with (map punit); intros als.
    - induction als.
      + unfold map; constructor.
      + simpl; constructor.
        * apply punit_unit.
        * assumption.
    - induction als; intros b c HH; inv HH.
      + reflexivity.
      + f_equal.
        * apply join_punit with a; assumption.
        * apply IHals. assumption.
  Qed.
  
  Instance Canc_list {CA: Canc_alg A}: Canc_alg (list A).
  Proof.
   intro. induction a1; intros; inv H; inv H0; auto.
    f_equal.
     eapply join_canc;eauto.
   eapply IHa1; eauto.
  Qed. 

  Instance Disj_list {DAa: Disj_alg A} : Disj_alg (list A).
  Proof. intro. induction a; intros; inv H; auto.
    f_equal; auto.
  Qed.

End sa_list.
Existing Instance Join_list. 
Existing Instance Perm_list.
Existing Instance Sep_list.
Existing Instance Core_list.
(*Existing Instance Unit_list.*)
Existing Instance PUnit_list.
Existing Instance Canc_list.
Existing Instance Disj_list.

Definition raw_join_hom A B (j1: A -> A -> A -> Prop) (j2: B -> B -> B -> Prop) (f:A ->B) :=
  forall x y z,
    j1 x y z ->
    j2 (f x) (f y) (f z).
Implicit Arguments raw_join_hom.

(** The SA induced by the preimage of a section
    in a section-retraction pair.

    This SA construction is used to generate
    a separation algebra over "knots".
 *)
Section sa_preimage.
  Variables A B:Type.
  Variable B_J: Join B.
   Variable PA: Perm_alg B.
 
  Variable f:A -> B.
  Variable f':B -> A.
  
  Hypothesis Hf'_f : forall x, f' (f x) = x.
  Hypothesis Hf_f' : join_hom (f oo f'). 
  
  Lemma f_inj : forall x y : A,  f x = f y -> x = y.
  Proof.
    intros.
    rewrite <- (Hf'_f x).
    rewrite <- (Hf'_f y).
    rewrite H; auto.
  Qed.

  Instance Join_preimage: Join A := 
          fun a b c => join (f a) (f b) (f c).

  Instance Perm_preimage  : @Perm_alg _  Join_preimage.
  Proof.
    constructor; simpl; intros.
    constructor; simpl; intros.
   do 2 red in H,H0.
   apply f_inj. 
   apply (join_eq H H0).

    do 2 red in H,H0.
    destruct (join_assoc H H0) as [z [? ?]].
    exists (f' z).
    split;
     [ do 2 red; rewrite <- (Hf'_f b); rewrite <- (Hf'_f c)
     | do 2 red; rewrite <- (Hf'_f a); rewrite <- (Hf'_f e)];
    apply Hf_f'; auto.

    do 2 red in H|-*; auto.

    apply f_inj; eapply join_positivity; eauto.
 Qed.

  Instance Sep_preimage {SAb: Sep_alg B}: Sep_alg A.
  Proof.
    apply mkSep with (fun x : A => f' (core (f x))); intros.
 
    do 3 red.
   generalize (@Hf_f' (@core B B_J SAb (f t)) (f t) (f t) (core_unit _)); intro.
   unfold compose in H. rewrite Hf'_f in H. auto.
   do 2 red in H.
   f_equal; apply (join_core H).
 Defined.
  
  Instance Core_preimage {CAb: Core_alg B}
           (fcore: forall a:A, core (f a) = f (core a))
           (*PEa: Perm_alg A *): Core_alg A.
  Proof.
    apply mkCore with (Sep_preimage).
    intros a H1.
    assert (H2: join (core a) a a) by
    apply core_unit.
    do 2 red in H1.
    do 2 red in H2.
    apply f_inj.
    rewrite (dup_core _ H1); auto.
    
    intros a b c H1.
    assert (H2: join (core c) a a).
    apply join_core in H1; rewrite core_idem in H1; rewrite <- H1.
    apply core_unit.

    (*Note this could end using positivity. 
      Since we used fcore in the previous goal, 
      we stick to that *)
    (*rewrite (join_positivity H1 H2) at 1; assumption.*)
    do 2 red in H1; rewrite <- fcore in H1.
    do 2 red. apply (split_core _ _ _ H1).
  Qed.
    
 Instance Sing_preimage {SAb: Sep_alg B}{Sing_b: Sing_alg B}: Sing_alg A.
 Proof.
 apply (mkSing (f' the_unit)).
 intro.
 simpl. rewrite <- (the_unit_core (f a)). f_equal; apply core_uniq.
 Defined.

 Instance Unit_preimage(* {SAb: Sep_alg B}*){Ub: Unital B} : Unital A.
 Proof.
   apply mkUnital with (f' (@join_unit _ _ Ub)).
   intros a. unfold join, Join_preimage.
   rewrite <- (Hf'_f a).
   apply Hf_f'.
   apply join_lid.
 Qed.

 (*Could it be proved without PrePCM.
   That is, without using join_eq
  *)
 Instance PUnit_preimage' {Ub:Unital B}{PUb: PartialUnital B} : PartialUnital A.
 Proof.
   apply Unital_PUnital; auto.
   destruct Perm_preimage; auto.
   apply Unit_preimage.
 Qed.


 (*Need to assume units are surjective on f*)
 Instance PUnit_preimage {PUb: PartialUnital B}(PUff': forall b, punit b = (f oo f') (punit b)) : PartialUnital A.
 Proof.
   apply mkPUnital with (fun x : A => f' (punit (f x))); intros a.
   do 2 red.

   generalize (@Hf_f' (@punit B B_J PUb (f a)) (f a) (f a) (punit_unit)); intro H.
   unfold compose in H. rewrite Hf'_f in H. auto.

   (*clear PUff' .
   pose (e':=f' (punit (f a))); fold e'.
   intros b c HH. do 2 red in HH.
   generalize (join_punit (f e') _ _ HH).*)
   
   intros b c HH.
   do 2 red in HH.
   apply f_inj.
   unfold compose in PUff';
   rewrite <- PUff' in HH.
   apply join_punit with (f a); assumption.
 Qed.
 
 (*NOTE: I don't believe this can be proven. The hom hypothesis is too weak. *)
 (*Instance PUnit_preimage {PUb: PartialUnital B} : PartialUnital A.
 Proof.
    apply mkPUnital with (fun x : A => f' (punit (f x))); intros.
    - unfold join, Join_preimage.
      
      destruct PUb. generalize (punit_unit (f a)).
      intros. apply Hf_f' in H; unfold compose in H.
      rewrite Hf'_f in H; auto.
   
    - simpl. intros b c HH.
      do 2 red in HH.
      
      
      rewrite <- (Hf'_f b), <- (Hf'_f c).
      apply f_inj. apply join_punit with (f a).
      unfold join, Join_preimage in HH.
      apply Hf_f' in HH; unfold compose in HH.
     rewrite <- (Hf'_f b), <- (Hf'_f c).
     apply Hf_f'; auto.
 Qed.*)
 
 Instance Canc_preimage {SAb: Sep_alg B}{CAb: Canc_alg B} : Canc_alg A.
 Proof. intros ? ? ? ? ? ?. do 2 red in H,H0.
  generalize (join_canc H H0); intro.
  apply f_inj; auto.
 Qed.

 Instance Disj_preimage {SAb: Sep_alg B}{DAb: Disj_alg B} : Disj_alg A.
  Proof. repeat intro. do 2 red in H. apply join_self in H. apply f_inj; auto. 
  Qed.

End sa_preimage.

Existing Instance Join_preimage. 
Existing Instance Perm_preimage.
Existing Instance Sep_preimage.
Existing Instance Core_preimage.
Existing Instance Sing_preimage.
Existing Instance Unit_preimage.
Existing Instance PUnit_preimage'.
Existing Instance Canc_preimage.
Existing Instance Disj_preimage.

Section SepAlgBijection.
  Variables (A: Type) (Ja: Join A)(PAa: Perm_alg A).
  Variable B:Type.

  Variable bij : bijection A B.
  Instance Join_bij: Join B := fun (x y z : B) => join (bij_g _ _ bij x) (bij_g _ _ bij y) (bij_g _ _ bij z).

  Lemma Perm_bij  : Perm_alg B.
  Proof.
    constructor; intros.
    constructor; intros.

    do 2 red in H,H0.
    generalize (join_eq H H0); clear H H0; intro.
    rewrite <- (bij_fg _ _ bij z). rewrite <- (bij_fg _ _ bij z'). f_equal; auto.

    do 2 red in H,H0.
   destruct (join_assoc H H0) as [m [? ?]]; exists (bij_f _ _ bij m); split;
   do 2 red; rewrite bij_gf; auto.

    do 2 red in H|-*. apply join_comm; auto.

    do 2 red in H,H0. rewrite <- (bij_fg _ _ bij a); rewrite <- (bij_fg _ _ bij b).
    f_equal. eapply join_positivity; eauto.
   Qed.


  Instance Sep_bij {SAa: Sep_alg A} : Sep_alg B.
  Proof. 
   apply mkSep with (fun b => bij_f _ _ bij (core (bij_g _ _ bij b))); intros.
   do 3 red.
   repeat rewrite bij_gf. simpl. apply core_unit.
   do 2 red in H. f_equal. apply (join_core H).
  Defined.

  Instance Core_bij {CAa: Core_alg A} : Core_alg B.
  Proof.
    pose (g:=bij_g _ _ bij); pose (f:= bij_f _ _ bij).
    apply mkCore with Sep_bij.
    intros. do 2 red in H; fold g in H.
    unfold core, Sep_bij. fold f g.
    eapply bij_g_inj with bij; fold g.
    rewrite (bij_gf _ _ bij).
    apply (dup_core _ H).

    intros a b c HH.
    do 2 red. fold f g.
    do 2 red in HH; unfold core, Sep_bij in HH; fold f g in HH. 
    rewrite (bij_gf _ _ bij) in HH.
    eapply (split_core _ _ _ HH).
  Qed.
    
    
 Lemma Sing_bij {SAa: Sep_alg A}{SingA: Sing_alg A} : Sing_alg B.
  Proof.
   apply (mkSing (bij_f _ _ bij the_unit)); intros.
   simpl. f_equal. apply  (the_unit_core (bij_g _ _ bij a)).
  Defined.

  Instance Unit_bij {Ua: Unital A} : Unital B.
  Proof.
    apply mkUnital with (bij_f  _ _ bij join_unit).
    intros. unfold join, Join_bij.
    rewrite (bij_gf _ _ bij); apply join_lid.
  Qed.
  
  Instance PUnit_bij {PUa: PartialUnital A} : PartialUnital B.
  Proof.
    pose (g:=bij_g _ _ bij); pose (f:= bij_f _ _ bij).
    apply mkPUnital with (fun e => f (punit (g e))); intros a.
    unfold join, Join_bij; repeat rewrite (bij_gf _ _ bij). apply punit_unit.

    intros b c HH.
    cut (g b = g c).
    { intros H; rewrite <- (bij_fg _ _ bij b); rewrite <- (bij_fg _ _ bij c).
        repeat fold g. rewrite H. reflexivity. }
    apply join_punit with (g a).
    revert HH; unfold join, Join_bij.
    repeat rewrite (bij_gf _ _ bij). fold g. trivial.
  Qed.
  
 Instance Canc_bij {CAa: Canc_alg A} : Canc_alg B.
  Proof. repeat intro.
    do 2 red in H,H0.
    generalize (join_canc H H0);intro.
    rewrite <- (bij_fg _ _ bij a1). rewrite <- (bij_fg _ _ bij a2). rewrite H1; auto.
  Qed.

  Instance  Disj_bij {DAa: Disj_alg A} : Disj_alg B.
  Proof. repeat intro. do 2 red in H.
    apply join_self in H.
   rewrite <- (bij_fg _ _ bij a). rewrite <- (bij_fg _ _ bij b). rewrite H; auto.
  Qed.

End SepAlgBijection.
Existing Instance Join_bij. 
Existing Instance Perm_bij.
Existing Instance Sep_bij.
Existing Instance Core_bij.
Existing Instance Sing_bij.
Existing Instance Unit_bij.
Existing Instance PUnit_bij.
Existing Instance Canc_bij.
Existing Instance Disj_bij.
