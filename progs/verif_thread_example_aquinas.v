Require Import floyd.proofauto.
Require Import progs.thread_example_aquinas.

(* We do not yet call threadlib, here, because we are modifying the
   pre- and postconditions *)

Instance CompSpecs : compspecs.
Proof. make_compspecs prog. Defined.

Local Open Scope logic.

Definition natural_alignment := 8.

Ltac simplify_value_fits' :=
  rewrite ?proj_sumbool_is_true by auto;
   rewrite ?proj_sumbool_is_false by auto;
   try
    match goal with
    |- context [value_fits ?sh ?t ?v] =>
        let t' := fresh "t" in
        set (t' := t); hnf in t'; subst t'; rewrite (value_fits_ind sh _ v);
        match goal with
         |- context [unfold_reptype v] =>
             change (unfold_reptype v) with v
         end; rewrite ?Z.max_r by (try computable; omega)
    end.

Axiom lock_inv : share -> val -> mpred -> mpred.

Axiom lock_inv_share_join : forall sh1 sh2 sh l R, sepalg.join sh1 sh2 sh ->
  lock_inv sh1 l R * lock_inv sh2 l R = lock_inv sh l R.

Axiom lock_inv_isptr : forall sh l R, lock_inv sh l R |-- !!(isptr l).

Axiom lock_inv_separate : forall sh1 sh2 l R1 R2, lock_inv sh1 l R1 * lock_inv sh2 l R2 |-- FF.

Axiom hold : val -> mpred -> mpred.

Axiom tight : mpred -> Prop.
Axiom tightly : mpred -> mpred.
Axiom tightly_eq : forall R, tight R -> tightly R = R.

Definition tlock := Tstruct _lock_t noattr.

Definition makelock_spec R :=
   WITH l : val, sh : share
   PRE [ 1%positive OF tptr tlock ]
     PROP (writable_share sh)
     LOCAL (temp 1%positive l)
     SEP (`(data_at_ sh tlock l))
   POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (`(lock_inv sh l R); `(hold l R)).

Definition freelock_spec R :=
   WITH l : val, sh : share
   PRE [ 1%positive OF tptr tlock ]
     PROP (writable_share sh)
     LOCAL (temp 1%positive l)
     SEP (`(lock_inv sh l R); `(hold l R))
   POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (`(data_at_ sh tlock l)).

Definition acquire_spec R :=
   WITH l : val, sh : share
   PRE [ 1%positive OF tptr tlock ]
     PROP (readable_share sh)
     LOCAL (temp 1%positive l)
     SEP (`(lock_inv sh l R))
   POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (`(lock_inv sh l R); `(tightly R)).

Definition release_spec R := (* no need for the share *)
   WITH l : val
   PRE [ 1%positive OF tptr tlock ]
     PROP (tight R; exists R', (R = R' * hold l (|> R))%logic)
     LOCAL (temp 1%positive l)
     SEP (`R)
   POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP ().

Definition voidstar_funtype :=
  Tfunction
    (Tcons (tptr tvoid) Tnil)
    (tptr tvoid)
    cc_default.

(* Discussion about spawn_thread:

1) As in makelock/acquire/... we get a universe inconsistency when we
add "WITH P" to the specification.  As a hack, I have introduced a
placeholder of type [val -> mpred] that you have to substitute to your
own R each time you use this function.

2) Potential improvements:

  a) We might add a parameter for "PROP" but it's not necessary,
     because we can encode it in SEP.

  b) We might state an alpha-conversion theorem () and then replace EX
     _y .. _y with "1%positive"

3) Likely an improvement: instead of LOCAL (temp _y y), make it LOCALx
   (temp _y y :: Q) with Q composed only on gvar s.

4) Likely an improvement: instead of requiring a specification for the
   spawned function that is of a very restricted form in [funspec
   (WITH .. PRE .. POST ..) f] in SEP, we might introduce a notion of
   subspecification [subspec] and require [funspec spec f] in SEP and
   [subspec spec (WITH .. PRE .. POST ..)] in PROP.  However, this
   needs to have a [WITH spec : funspec] in the specification of
   spawn_thread which currently yields a universe inconsistency.

*)

Definition spawn_thread_spec P :=
   WITH f : val, b : val
   PRE [1%positive OF tptr voidstar_funtype, 2%positive OF tptr tvoid]
     PROP ()
     LOCAL (temp 1%positive f; temp 2%positive b)
     SEP ((EX _y : ident, `(func_ptr'
       (WITH y : val
          PRE [ _y OF tptr tvoid ]
            PROP  ()
            LOCAL (temp _y y)
            SEP   (`(P y))
          POST [tptr tvoid]
            PROP  ()
            LOCAL ()
            SEP   ()
       )
       f));
     `(P b))
   POST [ tvoid ]
     PROP  ()
     LOCAL ()
     SEP   (emp).

Definition exit_thread_spec (_ : unit) :=
   WITH u:unit
   PRE [ ]
     PROP ()
     LOCAL ()
     SEP (emp)
   POST [ tvoid ]
     PROP  ()
     LOCAL ()
     SEP   (`FF).

(* We list the specifications that we assume.  In the future,
   identifier for those functions would be strings instead of
   positives. *)

Definition threadlib_specs : list (ident * {x : Type & x -> funspec}) := [
  (_makelock    , existT _                       mpred          makelock_spec);
  (_freelock    , existT _                       mpred          freelock_spec);
  (_acquire     , existT _                       mpred          acquire_spec);
  (_release     , existT _                       mpred          release_spec);
  (_spawn_thread, existT _                       (val -> mpred) spawn_thread_spec)
(*;(_exit_thread , existT (fun x => x -> funspec) unit           exit_thread_spec)*)
].

Fixpoint find_in_list {A B} (D:forall x y : A, {x = y} + {x <> y})
  (a : A) (l : list (A * B)) : option B :=
  match l with
    | nil => None
    | (a', b) :: l => if D a a' then Some b else find_in_list D a l
  end.

Definition find_in_threadlib_specs id := find_in_list peq id threadlib_specs.

(* Same lemma as [semax_call_id00_wow] but it concerns only the
   functions listed in [threadlib_specs], which, in addition to being
   external, need an additional parameter [witness'] of type, for
   example, [mpred], on which quantifying directly in the WITH clause
   would result in a universe inconsistency. *)
Lemma semax_call_id00_wow_threadlib :
 forall  {A} {A'} (witness: A) (witness': A') (Frame: list mpred) 
           Espec {cs: compspecs} Delta P Q R id (paramty: typelist) (bl: list expr)
                  (argsig: list (ident * type)) (Pre Post: A -> environ -> mpred)
                  ffunspec
             (Post2: environ -> mpred)
             (Ppre: list Prop)
             (Qpre: list (environ -> Prop))
             (Qtemp Qactuals Qpre_temp : PTree.t _)
             (Qvar Qpre_var: PTree.t vardesc)
             (B: Type)
             (Ppost: B -> list Prop)
             (Rpre: list (environ -> mpred))
             (Rpost: B -> list (environ -> mpred))
             (Rpost': B -> list mpred)
             (R' Rpre' : list mpred)
             (vl : list val)
   (GLBL: (var_types Delta) ! id = None)
   (NAME: find_in_threadlib_specs id = Some (existT (fun x => x -> funspec) A' ffunspec))
   (FUNSPEC: ffunspec witness' = mk_funspec (argsig, Tvoid) A Pre Post)
   (* (GLOBS: (glob_specs Delta) ! id = Some (mk_funspec (argsig,Tvoid) A Pre Post)) *)
   (* (GLOBT: (glob_types Delta) ! id = Some (type_of_funspec (mk_funspec (argsig,Tvoid) A Pre Post))) *)
   (H: paramty = type_of_params argsig)
   (PTREE: local2ptree Q Qtemp Qvar nil nil)
   (EXTRACT: extract_trivial_liftx R R')
   (TC1: PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R))
          |-- (tc_exprlist Delta (argtypes argsig) bl))
   (PRE1: Pre witness = PROPx Ppre (LOCALx Qpre (SEPx Rpre)))
   (PTREE': local2ptree Qpre Qpre_temp Qpre_var nil nil)
   (EXTRACT': extract_trivial_liftx Rpre Rpre')
   (MSUBST: force_list (map (msubst_eval_expr Qtemp Qvar) 
                    (explicit_cast_exprlist (argtypes argsig) bl))
                = Some vl)
   (PTREE'': pTree_from_elements (List.combine (var_names argsig) vl) = Qactuals)
   (CHECKTEMP: PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) 
           |-- !! Forall (check_one_temp_spec Qactuals) (PTree.elements Qpre_temp))
   (CHECKVAR: PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R))
           |-- !! Forall (check_one_var_spec Qvar) (PTree.elements Qpre_var))
   (FRAME: fold_right sepcon emp R' |-- fold_right sepcon emp Rpre' * fold_right sepcon emp Frame)
   (POST1: Post witness = (EX vret:B, PROPx (Ppost vret) (LOCALx nil (SEPx (Rpost vret)))))
   (EXTRACT'': forall vret, extract_trivial_liftx (Rpost vret) (Rpost' vret))
   (POST2: Post2 = EX vret:B, PROPx (P++ Ppost vret ) (LOCALx Q
             (SEPx (map liftx (Rpost' vret ++ Frame)))))
   (PPRE: fold_right_and True Ppre),
   @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R)))
    (Scall None
             (Evar id (Tfunction paramty Tvoid cc_default))
             bl)
    (normal_ret_assert Post2).
Proof.
Admitted.

(* We need different tactics for them, if only because we have an
   additional witness, which would conflict with the intropattern
   notation. *)

Ltac forward_call_id00_wow_threadlib witness witness' :=
let Frame := fresh "Frame" in
 evar (Frame: list (mpred));
 eapply (semax_call_id00_wow_threadlib witness witness' Frame);
 [ reflexivity | reflexivity | reflexivity | reflexivity
 | prove_local2ptree | repeat constructor 
 | try apply local_True_right; entailer!
 | reflexivity
 | prove_local2ptree | repeat constructor 
 | reflexivity | reflexivity
 | Forall_pTree_from_elements
 | Forall_pTree_from_elements
 | unfold fold_right at 1 2; cancel
 | cbv beta iota; 
    repeat rewrite exp_uncurry;
    try rewrite no_post_exists0; 
    first [reflexivity | extensionality; simpl; reflexivity]
 | intros; try match goal with  |- extract_trivial_liftx ?A _ =>
        (has_evar A; fail 1) || (repeat constructor)
     end
 | unify_postcondition_exps
 | unfold fold_right_and; repeat rewrite and_True; auto
 ].

Ltac fwd_call'_threadlib witness witness' :=
 try match goal with
      | |- semax _ _ (Scall _ _ _) _ => rewrite -> semax_seq_skip
      end;
 first [
     revert witness; 
     match goal with |- let _ := ?A in _ => intro; fwd_call'_threadlib A witness'
     end
   | eapply semax_seq';
     [first [forward_call_id1_wow witness
           | forward_call_id1_x_wow witness
           | forward_call_id1_y_wow witness
           | forward_call_id01_wow witness ]
     | after_forward_call
     ]
  |  eapply semax_seq'; [forward_call_id00_wow_threadlib witness witness'
          | after_forward_call ]
  | rewrite <- seq_assoc; fwd_call'_threadlib witness
  ].

Tactic Notation "forward_call_threadlib" constr(witness) constr(witness') simple_intropattern_list(v) :=
    (* (* we don't need this check (as our specs are canonical),
          and it stack overflows *)
    check_canonical_call; *)
    check_Delta;
    fwd_call'_threadlib witness witness';
  [ .. 
  | first 
      [ (* body of uniform_intros tactic *)
         (((assert True by (intros v; apply I);
            assert (forall a: unit, True) by (intros v; apply I);
            fail 1)
          || intros v) 
        || idtac);
        (* end body of uniform_intros tactic *)
        match goal with
        | |- semax _ _ _ _ => idtac 
        | |- unit -> semax _ _ _ _ => intros _ 
        end;
        repeat (apply semax_extract_PROP; intro);
       abbreviate_semax;
       try fwd_skip
     | complain_intros
     ]  
  ].


(* ideally the function spec would be like this, but we have to fit
   the precondition of spawn.  Fortunately, we should be able to
   relate the two through semax_body. *)
(*
Definition f_spec :=
 DECLARE _f
  WITH args_ : val, l_ : reptype tlock, sh : share
  PRE [ _args OF tptr tvoid ]
     PROP (readable_share sh)
     LOCAL (temp _args args_)
     SEP (`(field_at sh (Tstruct _ab noattr) [StructField _lock] l_ args_);  (* obsolete? *)
          `(lock_inv sh args_ Rlock_placeholder))
  POST [ tptr tvoid ]
     PROP ()
     LOCAL ()
     SEP ().
*)

(* Operator building resource invariants of the form R = S * hold l R *)

Definition contractive (F : mpred -> mpred) := HOcontractive (fun P (_ : unit) => F (P tt)).

Lemma contractive_entail F : contractive F -> forall P Q, |> P <=> |> Q |-- F P >=> F Q.
Proof.
  intros C P Q.
  specialize (C (fun _ => P) (fun _ => Q)).
  eapply derives_trans; [ eapply derives_trans | ]; [ | apply C | ].
    apply allp_right; intros [].
    rewrite fash_andp, fash_andp, later_andp.
    apply andp_derives; rewrite subp_later; apply derives_refl.
  
  apply allp_left, fash_derives, andp_left1, derives_refl.  apply tt.
Qed.

Definition Rec (F : mpred -> mpred) : mpred := HORec (fun P _ => F (P tt)) tt.

Lemma Rec_fold_unfold F : contractive F -> Rec F = F (Rec F).
Proof.
  unfold contractive, Rec; intros C.
  etransitivity; [ rewrite HORec_fold_unfold | ]; auto.
Qed.

Definition nonexpansive (F : mpred -> mpred) := HOnonexpansive (fun P (_ : unit) => F (P tt)).

Lemma nonexpansive_entail F : nonexpansive F -> forall P Q, P <=> Q |-- F P <=> F Q.
Proof.
  intros N P Q.
  specialize (N (fun _ => P) (fun _ => Q)).
  eapply derives_trans; [ eapply derives_trans | ]; [ | apply N | ].
  now apply allp_right.
  now apply allp_left.
Qed.

Axiom nonexpansive_lock_inv : forall sh p, nonexpansive (lock_inv sh p).

Axiom nonexpansive_hold : forall l, nonexpansive (hold l).

Axiom lock_inv_later : forall sh p R, lock_inv sh p R |-- lock_inv sh p (|> R).

Axiom hold_later : forall p R, hold p R |-- hold p (|> R).

Definition selfhold l (S : mpred -> mpred) := Rec (fun P => S P * hold l (|> P)).

Lemma prove_contractive F : (forall P Q, |> P <=> |> Q |-- F P >=> F Q) -> contractive F.
Proof.
  intros C; apply prove_HOcontractive; intros P Q HOH.
  apply allp_left with tt, C.
Qed.

Lemma selfhold_eq l S :
  contractive S ->
  selfhold l S = S (selfhold l S) * hold l (|> selfhold l S).
Proof.
  intros CS.
  unfold selfhold; apply Rec_fold_unfold, prove_contractive; intros P Q.
  apply subp_sepcon.
    eapply derives_trans.
      apply contractive_entail, CS. apply derives_refl.
    eapply derives_trans.
      apply nonexpansive_entail, nonexpansive_hold.
      apply fash_derives, andp_left1, derives_refl.
Qed.

(* shares *)

Lemma split_readable_share sh :
  readable_share sh ->
  exists sh1, exists sh2,
    readable_share sh1 /\
    readable_share sh2 /\
    sepalg.join sh1 sh2 sh.
Admitted.

Lemma split_Tsh :
  exists sh1, exists sh2,
    readable_share sh1 /\
    readable_share sh2 /\
    sepalg.join sh1 sh2 Tsh.
Proof.
  apply split_readable_share; auto.
Qed.

Axiom sh1 sh2 : share.
Axiom Rsh1 : readable_share sh1.
Axiom Rsh2 : readable_share sh2.
Axiom JoinTsh : sepalg.join sh1 sh2 Tsh.


(* The following resource is the actual data that we want to pass *)

Definition data_res' p P :=
  EX v : Z,
    field_at Tsh (Tstruct _t noattr) [StructField _p1] (Vint (Int.repr v)) p *
    field_at Tsh (Tstruct _t noattr) [StructField _p2] (Vint (Int.repr v)) p *
    (field_at Tsh (Tstruct _t noattr) [StructField _p3] (Vint (Int.repr 1)) p
    ||
    (field_at Tsh (Tstruct _t noattr) [StructField _p3] (Vint (Int.repr 0)) p *
    lock_inv sh2 p (|> P))).

Definition data_res p := selfhold p (data_res' p).

Lemma data_res_eq p : data_res p = data_res' p (data_res p) * hold p (|> data_res p).
Proof.
  unfold data_res at 1.
  rewrite selfhold_eq. reflexivity.
  apply prove_contractive; intros P Q.
  unfold data_res'.
  apply subp_exp; intros v.
  apply subp_sepcon. apply subp_refl.
  apply subp_orp. apply subp_refl.
  apply subp_sepcon. apply subp_refl.
  eapply derives_trans.
    apply nonexpansive_entail, nonexpansive_lock_inv.
    apply fash_derives, andp_left1, derives_refl.
Qed.

Lemma data_res_eq_verbose p : data_res p = EX v : Z,
    field_at Tsh (Tstruct _t noattr) [StructField _p1] (Vint (Int.repr v)) p *
    field_at Tsh (Tstruct _t noattr) [StructField _p2] (Vint (Int.repr v)) p *
    (field_at Tsh (Tstruct _t noattr) [StructField _p3] (Vint (Int.repr 1)) p
    ||
    (field_at Tsh (Tstruct _t noattr) [StructField _p3] (Vint (Int.repr 0)) p *
    lock_inv sh2 p (|> data_res p))) *
    hold p (|> data_res p).
Proof.
  rewrite data_res_eq at 1.
  unfold data_res'.
  apply pred_ext; Intros v; Exists v; auto.
Qed.

Definition f_spec :=
 DECLARE _f
  WITH y : val
  PRE [ _y OF tptr tvoid ]
     PROP ()
     LOCAL (temp _y y)
     SEP (`(lock_inv sh2 y (data_res y)))
  POST [ tptr tvoid ]
     PROP ()
     LOCAL ()
     SEP ().

Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] PROP () LOCAL () SEP ()
  POST [ tint ] PROP () LOCAL () SEP ().

Definition Vprog : varspecs := (_f, Tfunction (Tcons (tptr tvoid) Tnil) (tptr tvoid) cc_default) :: nil.

Definition Gprog : funspecs := [f_spec; main_spec].

Lemma sepcon_lift_comm A B : `A * `B = `(A * B).
Proof.
  apply pred_ext; entailer.
Qed.

Lemma exp_fun_comm A B P : (fun b : B => (EX a : A, (P a b))) = exp P.
Proof.
  extensionality b.
  apply pred_ext; entailer.
  unfold exp; simpl.
  apply exp_right with a; auto.
Qed.

Lemma exp_lift_comm A P : (EX x : A, `(P x)) = `(EX x : A, P x).
Proof.
  apply pred_ext; entailer; eapply exp_right; eauto.
Qed.

Lemma andp_lift_comm A B : `A && `B = `(A && B).
Proof.
  apply pred_ext; entailer.
Qed.

Lemma semax_fun_id'' id f Espec {cs} Delta P Q R Post c :
  (var_types Delta) ! id = None ->
  (glob_specs Delta) ! id = Some f ->
  (glob_types Delta) ! id = Some (type_of_funspec f) ->
  @semax cs Espec Delta
    (EX v : val, PROPx P
      (LOCALx (gvar id v :: Q)
      (SEPx (`(func_ptr' f v) :: R)))) c Post ->
  @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R))) c Post.
Proof.
intros V G GS SA.
apply (semax_fun_id id f Delta); auto.
eapply semax_pre_post; try apply SA; [ clear SA | intros; entailer ].
go_lowerx.
apply exp_right with (eval_var id (type_of_funspec f) rho).
entailer.
apply andp_right.
- (* about gvar *)
  apply prop_right.
  unfold gvar, eval_var, Map.get.
  destruct H as (_ & _ & DG & DS).
  destruct (DS id _ GS) as [-> | (t & E)]; [ | congruence].
  destruct (DG id _ GS) as (? & -> & ?); auto.

- (* about func_ptr/func_ptr' *)
  unfold func_ptr'.
  rewrite <- andp_left_corable, andp_comm; auto.
  apply corable_func_ptr.
Qed.

Ltac get_global_function'' _f :=
  eapply (semax_fun_id'' _f); try reflexivity.

Ltac fold_field_at_' a :=
  try match a with
    | PROPx _ ?a => fold_field_at_' a
    | LOCALx _ ?a => fold_field_at_' a
    | SEPx ?l => fold_field_at_' l
    | `?h :: ?t => fold_field_at_' h; fold_field_at_' t
    | ?a * ?b => fold_field_at_' b; fold_field_at_' a
    | ?a && ?b => fold_field_at_' a; fold_field_at_' b
    | @mapsto ?cs ?sh ?ty ?val ?p => try replace (@mapsto cs sh ty val p) with (@mapsto_ cs sh ty p) by reflexivity
    | @data_at ?cs ?sh ?ty ?val ?p => try replace (@data_at cs sh ty val p) with (@data_at_ cs sh ty p) by reflexivity
    | @field_at ?cs ?sh ?ty ?path ?val ?p => try replace (@field_at cs sh ty path val p) with (@field_at_ cs sh ty path p) by reflexivity
    | nil => idtac
  end.

Ltac fold_field_at_ :=
  match goal with
    | |- semax _ ?a _ _ => fold_field_at_' a
    | |- ?a |-- ?b => fold_field_at_' a; fold_field_at_' b
  end.

Lemma field_compatible_tlock v :
  field_compatible (Tstruct _t noattr) [StructField _l] v ->
  field_compatible tlock [] v.
Proof.
  destruct v; unfold field_compatible; intuition.
  unfold size_compatible, sizeof in *; simpl in *.
  omega.
Qed.

Lemma semax_orp {E:OracleKind} {Delta P Q c R} : semax Delta P c R -> semax Delta Q c R -> semax Delta (P || Q) c R.
Proof.
  intros HP HQ.
  replace (P || Q) with (EX b:bool, if b then P else Q).
  + Intros b; destruct b; auto.
  + apply pred_ext.
    - Intros b; destruct b; [ apply orp_right1 | apply orp_right2 ]; auto.
    - apply orp_left; [ Exists true | Exists false ]; auto.
Qed.

Lemma semax_orp_SEP {E:OracleKind} {Delta P Q R} A B {c post} :
  semax Delta (PROPx P (LOCALx Q (SEPx (`A :: R)))) c post ->
  semax Delta (PROPx P (LOCALx Q (SEPx (`B :: R)))) c post ->
  semax Delta (PROPx P (LOCALx Q (SEPx (`(A || B) :: R)))) c post.
Proof.
  intros HA HB.
  apply semax_pre with
    (PROPx P (LOCALx Q (SEPx (`A :: R))) ||
     PROPx P (LOCALx Q (SEPx (`B :: R)))).
  entailer. rewrite distrib_orp_sepcon; auto.
  apply semax_orp; auto.
Qed.

Lemma distrib_sepcon_orp {A}{ND: NatDed A}{SL: SepLog A} (P Q R : A) : 
  sepcon R (P || Q) = sepcon R P || sepcon R Q.
Proof.
  intros.
  rewrite sepcon_comm, distrib_orp_sepcon.
  f_equal; apply sepcon_comm.
Qed.

Lemma orp_lift A B : `A || `B = `(A || B).
Proof.
  apply pred_ext; entailer.
Qed.

Lemma body_main : semax_body Vprog Gprog f_main main_spec.
Proof.
  name x _x.
  start_function.
  forward (* x.p1 = 0; *).
  forward (* x.p2 = 0; *).
  forward (* x.p3 = 1; *).
  forward (* i = 0; *).
  
  (* changing precondition to have [data_at_ Tsh tlock x] *)
  unfold_field_at 1%nat. normalize. fold _l _p1 _p2 _p3.
  rewrite field_at_data_at.
  fold_field_at_.
  assert_PROP (isptr x) as Px by entailer!.
  assert_PROP (field_compatible (Tstruct _t noattr) [StructField _l] x) as Fx by entailer!.
  assert_PROP (field_address (Tstruct _t noattr) [StructField _l] x = x) as Ex.
  { apply prop_right.
    unfold field_address, nested_field_offset2, nested_field_rec, field_offset, fieldlist.field_offset2, Ctypes.field_offset; simpl.
    if_tac; try tauto.  destruct x; inversion Px; simpl; f_equal; apply int_add_repr_0_r. }
  replace_SEP 0 (`(data_at_ Tsh tlock x)).
  { entailer.  rewrite Ex. apply derives_refl'; f_equal. }
  
  forward_call_threadlib (x, Tsh) (data_res x) (* makelock *).
  
  (* changing precondition to have [lock_inv sh2] *)
  rewrite <- (lock_inv_share_join _ _ _ _ _ JoinTsh); normalize.
  
  get_global_function'' _f; Intros f.
  forward_call_threadlib (f, x) (fun y => lock_inv sh2 y (data_res y)) (* spawn_thread(&f, &x) *).
  { rewrite exp_lift_comm. repeat constructor. }
  { simpl. Exists _y. cancel. }
  normalize. replace_SEP 0 (`emp).  admit (* Andrew? *).
  
  forward (* y = x.p3 *).
  
  pose (loop_inv :=
    @exp (environ->mpred) _ _ (fun i : Z =>
    @exp (environ->mpred) _ _ (fun y : bool =>
    @exp (environ->mpred) _ _ (fun j : Z =>
    PROP ()
    LOCAL (temp _i (Vint (Int.repr i));
           temp _y (Vint (Int.repr (if y then 1 else 0)));
           lvar _x (Tstruct _t noattr) x
    )
    SEP (`(lock_inv sh1 x (data_res x));
         `(hold x (data_res x));
         `(field_at Tsh (Tstruct _t noattr) [StructField _p1] (Vint (Int.repr j)) x);
         `(field_at Tsh (Tstruct _t noattr) [StructField _p2] (Vint (Int.repr j)) x);
         `(field_at Tsh (Tstruct _t noattr) [StructField _p3] (Vint (Int.repr (if y then 1 else 0))) x);
         `(if y then emp else lock_inv sh2 x (data_res x))
  ))))).
  forward_while loop_inv [[i y] j].
  { (* precondition *) Exists 0 true 0. entailer. }
  { (* typing *) apply prop_right, I. }
  { (* invariance *)
    destruct y; [ clear HRE | exfalso; apply HRE, eq_refl] (* y is 1 *).
    
    forward (* x.p1 = i; *).
    forward (* x.p2 = i; *).
    
    (* getting `(data_res x) in the precondition *)
    replace_SEP 1 (`(hold x (|> data_res x))) by (entailer!; apply hold_later).
    gather_SEP 1 2 3 4; replace_SEP 0 (`(data_res x)).
    rewrite data_res_eq; unfold data_res' at 2; rewrite <- data_res_eq. entailer.
    Exists i. entailer. cancel. apply orp_right1, derives_refl.
    
    forward_call_threadlib x (data_res x) (* release(&x.l); *).
    { repeat split; auto. admit. eexists; apply data_res_eq. }
    
    forward (* i++; *).
    
    forward_call_threadlib (x, sh1) (data_res x) (* acquire(&x.l); *).
    { apply Rsh1. }
    
    rewrite tightly_eq. 2:admit.
    rewrite data_res_eq; normalize; rewrite <-data_res_eq; unfold data_res'.
    forward_intro v.
    
    normalize.
    focus_SEP 2.
    apply semax_orp_SEP (* we split the orp in the precondition *).
    - forward.
      Exists (i + 1, true, v).
      entailer. cancel.
      admit (* can we solve this? *).
    
    - normalize.
      forward.
      Exists (i + 1, false, v).
      entailer.
      cancel.
      rewrite sepcon_comm; apply sepcon_derives.
      + admit (* again, reverse |> for hold *).
      + admit (* reverse |> for lock_inv *).
  }
  
  destruct y; [ inversion HRE | clear HRE ] (* y is 0 *).
  
  gather_SEP 0 5.
  rewrite sepcon_lift_comm, (lock_inv_share_join _ _ _ _ _ JoinTsh).
  
  forward_call_threadlib (x, Tsh) (data_res x) (* freelock(&x.l); *).
  
  forward (* y = x.p1; *).
  forward (* z = x.p2; *).
  match goal with |- semax _ ?Pre _ _ => forward_if Pre end (* if(y != z) i = *(int* )NULL; *).
  { (* case with dereferencing null pointer: we have a contraction in the hypothesis *)
    tauto. }
  { (* other case: skip *)
    forward. entailer. }
  
  forward (* return 0; *).
  
  (* cleaning up *)
  Exists x.
  entailer.
  unfold data_at_ at 2.
  unfold field_at_.
  unfold_field_at 4%nat. fold _l _p1 _p2 _p3.
  entailer.
  apply andp_right. apply prop_right, default_value_fits.
  unfold data_at_, field_at_.
  cancel.
  eapply derives_trans; [ | rewrite field_at_data_at; apply derives_refl ].
  unfold data_at.
  fold_field_at_.
  rewrite Ex.
  apply derives_refl'; f_equal.
Qed.


Lemma semax_loop_noincr {Espec} {CS: compspecs} Delta Q body R :
  @semax CS Espec Delta Q (Swhile (Econst_int (Int.repr 1) tint) body) R ->
  @semax CS Espec Delta Q (Sloop body Sskip) R.
Proof.
Admitted.

Tactic Notation "forward_while" constr(Inv)
     simple_intropattern(pat) :=
  repeat (apply -> seq_assoc; abbreviate_semax);
  first [ignore (Inv: environ->mpred) 
         | fail 1 "Invariant (first argument to forward_while) must have type (environ->mpred)"];
  apply semax_pre with Inv;
    [  unfold_function_derives_right 
    | eapply semax_seq;
      [repeat match goal with
       | |- semax _ (exp _) _ _ => fail 1
       | |- semax _ (PROPx _ _) _ _ => fail 1
       | |- semax _ ?Pre _ _ => match Pre with context [ ?F ] => unfold F end
       end;
       match goal with |- semax _ ?Pre _ _ =>
          let p := fresh "Pre" in let Hp := fresh "HPre" in 
          remember Pre as p eqn:Hp;
          repeat rewrite exp_uncurry in Hp; subst p
       end;
      match goal with |- semax ?Delta ?Pre (Swhile ?e _) _ =>
        eapply semax_while_3g1; 
        simpl typeof;
       [ reflexivity 
       | intros pat; simpl_fst_snd
       | (do_compute_expr1 Delta Pre e; eassumption || unfold tc_expr, denote_tc_assert; apply prop_right; tauto) (* CHANGED *)
       | intros pat; simpl_fst_snd; 
         let HRE := fresh "HRE" in apply semax_extract_PROP; intro HRE;
         first [simple apply typed_true_of_bool in HRE
               | apply typed_true_tint_Vint in HRE
               | apply typed_true_tint in HRE
               | idtac ];
         repeat (apply semax_extract_PROP; intro); 
         do_repr_inj HRE; normalize in HRE
        ]
       end
       | simpl update_tycon; 
         apply extract_exists_pre; intros pat; simpl_fst_snd;
         let HRE := fresh "HRE" in apply semax_extract_PROP; intro HRE;
         first [simple apply typed_false_of_bool in HRE
               | apply typed_false_tint_Vint in HRE
               | apply typed_false_tint in HRE
               | idtac ];
         repeat (apply semax_extract_PROP; intro)
       ]
     ]; abbreviate_semax; autorewrite with ret_assert.

Lemma body_f : semax_body Vprog Gprog f_f f_spec.
Proof.
  start_function.
  forward.
  drop_LOCAL 1%nat.
  assert_PROP (isptr y) as Py by (entailer; apply lock_inv_isptr).
  replace (force_val (sem_cast_neutral y)) with y by (destruct y; inversion Py; auto).
  apply semax_loop_noincr.
  match goal with |- semax _ ?Pre _ _ => pose (Inv:=(EX u : unit, Pre)) end.
  rewrite semax_seq_skip.
  forward_while Inv VAR; [ .. | inversion HRE (* loop never exits *) ].
  { Exists tt; entailer. }
  { apply prop_right, I. }
  
  forward (* skip *).
  forward_call_threadlib (y, sh2) (data_res y) (* acquire(&(x->l)); *).
  { apply Rsh2. }
  rewrite tightly_eq; [ | admit ].
  
  rewrite data_res_eq_verbose at 2.
  forward_intro v.
  normalize.
  forward (* temp = x->p1; *).
  forward (* x->p1 = temp * 2; *).
  forward (* temp = x->p2; *).
  forward (* x->p2 = temp * 2; *).
  forward (* temp = x->p1; *).
  
  rename v into n.
  forward_if ((PROP  ()  LOCAL  (temp _x y)  SEP  (`(data_res y); `(lock_inv sh2 y (data_res y))))) (* if(temp > 10) *).
    (* case with temp>10: we release everything *)
    
    (* refactor the disjunctive SEP *)
    replace_SEP 2 (`(EX b : bool,
       field_at Tsh (Tstruct _t noattr) [StructField _p3] (Vint (Int.repr (if b then 1 else 0))) y
        * if b then emp else lock_inv sh2 y (|>data_res y))).
    { entailer. apply orp_left; [Exists true | Exists false ]; entailer. }
    forward_intro b. normalize.
    
    forward (* x->p3 = 0; *).
    
    forward_call_threadlib y (data_res y) (* release(&(x->l)); *).
    { (* nothing is left in SEP after this call *)
      replace Frame with (@nil mpred) by (unfold Frame; reflexivity); simpl.
      rewrite data_res_eq_verbose at 4.
      Exists (n * 2)%Z.  cancel.
      apply orp_right2.  cancel.
      destruct b.
      + cancel; apply lock_inv_later.
      + (* contradiction *)  
        eapply derives_trans; [ apply lock_inv_separate | ]. entailer.
    }
    { split.
      + admit.
      + eexists. rewrite data_res_eq at 1. f_equal. }
      
    forward (* return; *).
    
    (* other case of the if: Some Sskip *)
    forward.
    entailer.
    rewrite data_res_eq_verbose at 4.
    Exists (n * 2)%Z.  cancel.
    
  (* after the if *)
  forward_call_threadlib y (data_res y) (* release(&(x->l)); *).
  { split.
    + admit.
    + eexists. rewrite data_res_eq at 1. f_equal. }
  
  (* maintain the invariant *)
  entailer.
Qed.
