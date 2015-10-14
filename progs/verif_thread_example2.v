Require Import floyd.proofauto.
Require Import progs.thread_example2.

(* We do not yet call threadlib, here, because we are modifying the
   pre- and postconditions *)

Instance CompSpecs : compspecs.
Proof. make_compspecs prog. Defined.

Local Open Scope logic.

Definition natural_alignment := 8.

Definition malloc_compatible (n: Z) (p: val) : Prop :=
  match p with
  | Vptr b ofs => (natural_alignment | Int.unsigned ofs) /\
                           Int.unsigned ofs + n < Int.modulus
  | _ => False
  end.

Lemma malloc_compatible_field_compatible:
  forall (cs: compspecs) t p n,
     sizeof cenv_cs t = n ->
     legal_alignas_type t = true ->
     legal_cosu_type t = true ->
     complete_type cenv_cs t = true ->
     (alignof cenv_cs t | natural_alignment) ->
     malloc_compatible n p ->
     field_compatible t nil p.
Proof.
intros.
subst n.
destruct p; simpl in *; try contradiction.
destruct H4.
pose proof (Int.unsigned_range i).
repeat split; simpl; auto; try omega.
clear - H3 H.
eapply Zdivides_trans; eauto.
Qed.

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

Definition malloc_spec :=
 DECLARE _malloc
  WITH n: Z
  PRE [ 1%positive OF tuint]
     PROP (4 <= n <= Int.max_unsigned)
     LOCAL (temp 1%positive (Vint (Int.repr n)))
     SEP ()
  POST [ tptr tvoid ]
     EX v: val,
     PROP (malloc_compatible n v)
     LOCAL (temp ret_temp v)
     SEP (`(memory_block Tsh n v)).

Definition tlock := Tstruct _lock_t noattr.

Axiom lock_inv : share -> val -> mpred -> mpred.

Axiom lock_inv_share_join : forall sh1 sh2 sh v R, sepalg.join sh1 sh2 sh ->
  lock_inv sh1 v R * lock_inv sh2 v R = lock_inv sh v R.

Axiom lock_inv_isptr : forall sh v R, lock_inv sh v R |-- !!(isptr v).

Axiom positive_mpred : mpred -> Prop.

Definition makelock_spec R :=
   WITH v : val, sh : share
   PRE [ _lock OF tptr tlock ]
     PROP (writable_share sh; predicates_sl.precise R; positive_mpred R)
     LOCAL (temp _lock v)
     SEP (`(data_at_ Tsh tlock v))
   POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (`(lock_inv Tsh v R)).

Definition freelock_spec R :=
   WITH v : val, sh : share
   PRE [ _lock OF tptr tlock ]
     PROP (writable_share sh)
     LOCAL (temp _lock v)
     SEP (`R ; `(lock_inv sh v R))
   POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (`R ; `(mapsto_ sh tlock v)).

Definition acquire_spec R :=
   WITH v : val, sh : share
   PRE [ _lock OF tptr tlock ]
     PROP (readable_share sh)
     LOCAL (temp _lock v)
     SEP (`(lock_inv sh v R))
   POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (`(lock_inv sh v R) ; `R).

Definition release_spec R :=
   WITH v : val, sh : share
   PRE [ _lock OF tptr tlock ]
     PROP (readable_share sh)
     LOCAL (temp _lock v)
     SEP (`(lock_inv sh v R) ; `R)
   POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (`(lock_inv sh v R)).

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
   PRE [_f OF tptr voidstar_funtype, _args OF tptr tvoid]
     PROP ()
     LOCAL (temp _args b)
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
  (_spawn_thread, existT _                       (val -> mpred) spawn_thread_spec);
  (_exit_thread , existT (fun x => x -> funspec) unit           exit_thread_spec)
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

(* To have a non-leaky return from the spawned function, we need a
   second lock with a self-referring resource invariant.  For this, we
   build an operator that takes a resource Q and return R such that R
   that is the product of Q and of a reference to R itself *)

Definition selflock_fun Q sh p : (unit -> mpred) -> (unit -> mpred) :=
  fun R _ => Q * lock_inv sh p (|> R tt).

Definition selflock' Q sh p : unit -> mpred := HORec (selflock_fun Q sh p).
Definition selflock Q sh p : mpred := selflock' Q sh p tt.

Definition nonexpansive F := HOnonexpansive (fun P (_ : unit) => F (P tt)).

Lemma nonexpansive_entail F : nonexpansive F -> forall P Q, P <=> Q |-- F P <=> F Q.
Proof.
  intros N P Q.
  specialize (N (fun _ => P) (fun _ => Q)).
  eapply derives_trans; [ eapply derives_trans | ]; [ | apply N | ].
  now apply allp_right.
  now apply allp_left.
Qed.

Axiom nonexpansive_lock_inv : forall sh p, nonexpansive (lock_inv sh p).

Lemma lock_inv_later sh p R : lock_inv sh p R |-- lock_inv sh p (|> R).
Admitted.

Lemma selflock'_eq Q sh p : selflock' Q sh p =
  selflock_fun Q sh p (selflock' Q sh p).
Proof.
  apply HORec_fold_unfold, prove_HOcontractive.
  intros P1 P2 u.
  apply subp_sepcon; [ apply subp_refl | ].
  eapply derives_trans. apply (nonexpansive_lock_inv sh p).
  apply allp_left with tt, fash_derives, andp_left1, derives_refl.
Qed.

Lemma selflock_eq Q sh p : selflock Q sh p = Q * lock_inv sh p (|> selflock Q sh p).
Proof.
  unfold selflock at 1.
  rewrite selflock'_eq.
  reflexivity.
Qed.

(* In fact we need locks to two resources:
   1) the resource invariant, for passing the resources
   2) the join resource invariant, for returning all resources, including itself
   for this we need to define them in a mutually recursive fashion: *)

Definition res_invariants_fun Q sh1 p1 sh2 p2 : (bool -> mpred) -> (bool -> mpred) :=
  fun R b =>
    if b then
      Q * lock_inv sh2 p2 (|> R false)
    else
      Q * lock_inv sh1 p1 (|> R true) * lock_inv sh2 p2 (|> R false).

Definition res_invariants Q sh1 p1 sh2 p2 : bool -> mpred := HORec (res_invariants_fun Q sh1 p1 sh2 p2).
Definition res_invariant Q sh1 p1 sh2 p2 : mpred := res_invariants Q sh1 p1 sh2 p2 true.
Definition join_res_invariant Q sh1 p1 sh2 p2 : mpred := res_invariants Q sh1 p1 sh2 p2 false.

Lemma res_invariants_eq Q sh1 p1 sh2 p2 : res_invariants Q sh1 p1 sh2 p2 =
  res_invariants_fun Q sh1 p1 sh2 p2 (res_invariants Q sh1 p1 sh2 p2).
Proof.
  apply HORec_fold_unfold, prove_HOcontractive.
  intros P1 P2 b.
  destruct b.
    (* resource invariant *)
    apply subp_sepcon; try apply subp_refl.
    apply allp_left with false.
    eapply derives_trans.
      apply nonexpansive_entail, nonexpansive_lock_inv.
      apply fash_derives, andp_left1, derives_refl.
    
    (* join resource invariant *)
    repeat apply subp_sepcon; try apply subp_refl.
      apply allp_left with true.
      eapply derives_trans.
        apply nonexpansive_entail, nonexpansive_lock_inv.
        apply fash_derives, andp_left1, derives_refl.
      
      apply allp_left with false.
      eapply derives_trans.
        apply nonexpansive_entail, nonexpansive_lock_inv.
        apply fash_derives, andp_left1, derives_refl.
Qed.

Lemma res_invariant_eq Q sh1 p1 sh2 p2 :
  res_invariant Q sh1 p1 sh2 p2 =
  Q *
  lock_inv sh2 p2 (|> join_res_invariant Q sh1 p1 sh2 p2).
Proof.
  unfold res_invariant at 1.
  rewrite res_invariants_eq.
  reflexivity.
Qed.

Lemma join_res_invariant_eq Q sh1 p1 sh2 p2 :
  join_res_invariant Q sh1 p1 sh2 p2 =
  Q *
  lock_inv sh1 p1 (|> res_invariant Q sh1 p1 sh2 p2) *
  lock_inv sh2 p2 (|> join_res_invariant Q sh1 p1 sh2 p2).
Proof.
  unfold join_res_invariant at 1.
  rewrite res_invariants_eq.
  reflexivity.
Qed.

(* The following resource is the actual data that we want to pass *)

Definition data_resource p :=
  EX n : Z,
    field_at Tsh (Tstruct _ab noattr) [StructField _a] (Vint (Int.repr n)) p *
    field_at Tsh (Tstruct _ab noattr) [StructField _b] (Vint (Int.repr (2 * n))) p.

(*
andrew wrote on the board:
{|> x|->y} i=[x] {i=y /\ x|->y}
{|> l []-> R} acquire(l) {R * l []-> R}

but it might be more like:
{ l []-> |>R } acquire(l) { R * l []-> |>R }
*)

Definition res_inv_1 p sh :=
  res_invariant (data_resource p) sh p sh (field_address (Tstruct _ab noattr) [StructField _join] p).

Definition res_inv_2 p sh :=
  join_res_invariant (data_resource p) sh p sh (field_address (Tstruct _ab noattr) [StructField _join] p).

Lemma res_inv_2_1 sh p :
  res_inv_2 p sh = res_inv_1 p sh *
  lock_inv sh p (|> res_inv_1 p sh).
Proof.
  unfold res_inv_1, res_inv_2.
  unfold res_invariant at 1, join_res_invariant.
  rewrite res_invariants_eq.
  simpl.
  apply pred_ext; cancel.
Qed.

Definition f_spec :=
 DECLARE _f
  WITH args_ : val
  PRE [ _args OF tptr tvoid ]
     PROP ()
     LOCAL (temp _args args_)
     SEP (`(EX sh : share,
       !!(readable_share sh) && lock_inv sh args_ (res_inv_1 args_ sh)))
  POST [ tptr tvoid ]
     PROP ()
     LOCAL ()
     SEP ().

Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] PROP () LOCAL () SEP ()
  POST [ tint ] PROP () LOCAL (temp ret_temp (Vint (Int.repr 4))) SEP ().

Definition Vprog : varspecs := (_f, Tfunction (Tcons (tptr tvoid) Tnil) (tptr tvoid) cc_default) :: nil.

Definition Gprog : funspecs :=
  malloc_spec :: f_spec :: main_spec::nil.

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
  field_compatible (Tstruct _ab noattr) [StructField _lock] v ->
  field_compatible tlock [] v.
Proof.
  destruct v; unfold field_compatible; intuition.
  unfold size_compatible, sizeof in *; simpl in *.
  omega.
Qed.

Lemma field_compatible_tlock_join v :
  field_compatible (Tstruct _ab noattr) [StructField _join] v ->
  field_compatible tlock [] (field_address (Tstruct _ab noattr) [StructField _join] v).
Proof.
  intros F; pose proof F as F'; revert F'. 
  destruct v; unfold field_compatible, field_address; if_tac; intuition;
  assert (Int.unsigned i + 24 < Int.modulus) by (simpl in *; omega).
  - (* size *)
    unfold nested_field_offset2, nested_field_rec, field_offset, fieldlist.field_offset2, Ctypes.field_offset; simpl in *.
    rewrite Int.unsigned_add_carry; unfold Int.add_carry, Int.unsigned in *.
    if_tac; simpl in *; omega.
  - (* alignment *)
    unfold nested_field_offset2, nested_field_rec, field_offset, fieldlist.field_offset2, Ctypes.field_offset; simpl.
    match goal with [ H : align_compatible _ _ |- _ ] => destruct H as [x A] end.
    rewrite Int.unsigned_add_carry; unfold Int.add_carry, Int.unsigned in *.
    if_tac; simpl in *; [ | omega ].
    exists (x + 6).
    rewrite A; unfold align_attr; simpl.
    omega.
Qed.

Tactic Notation "assert_PROP" constr(A) :=
  first [apply (assert_PROP A) | apply (assert_PROP' A)]; [ | intro ].
Tactic Notation "assert_PROP" constr(A) "by" tactic(t) :=
  first [apply (assert_PROP A) | apply (assert_PROP' A)]; [ now t | intro ].
Tactic Notation "assert_PROP" constr(A) "as" simple_intropattern(H)  :=
  first [apply (assert_PROP A) | apply (assert_PROP' A)]; [ | intro H ].
Tactic Notation "assert_PROP" constr(A) "as" simple_intropattern(H) "by" tactic(t) :=
  first [apply (assert_PROP A) | apply (assert_PROP' A)]; [ now t | intro H ].

Lemma body_main : semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  
  (* COMMAND: ab = malloc(..) *)
  (* when forward_call fails, be sure to check that the type of your
  specification matches exactly the type of the function, for example
  here I copy-pasted a specification for mallocN found in verif_queue
  that used tint instead of tuint for the regular malloc *)
  forward_call 56%Z ab_.
  now match goal with [|-_<=_<=_] => compute; intuition; congruence end.
  
  (* transforming memory_block into field_at_ *)
  replace_SEP 0 (`(field_at_ Tsh  (Tstruct _ab noattr) [] ab_)).
  { entailer. rewrite field_at__memory_block. simpl. unfold field_address. simpl.
    if_tac; [ now entailer | ].
    exfalso; apply H0.
    unfold field_compatible.
    intuition; simpl; try reflexivity; destruct _id; simpl; auto; unfold malloc_compatible in *; intuition.
    unfold natural_alignment, align_attr in *; simpl in *.
    match goal with [ H : ( _ | _ ) |- _ ] => destruct H as [x Ex] end.
    exists (2 * x)%Z; omega. }
  
  (* split the frame to extract the lock *)
  (* before calling makelock, we save this [field_compatible] fact, needed for the next makelock *)
  unfold field_at_.
  unfold_field_at 1%nat.
  fold _a _b _lock _join.
  fold_field_at_.
  normalize.
  assert_PROP (field_compatible (Tstruct _ab noattr) [StructField _lock] ab_) as Fl by entailer.
  assert_PROP (field_compatible (Tstruct _ab noattr) [StructField _join] ab_) as Fj by entailer.
  
  (* COMMAND: makelock(); *)
  (* establish the lock invariant *)
  destruct split_Tsh as (sh1 & sh2 & Rsh1 & Rsh2 & Join).
  forward_call_threadlib (ab_, Tsh) (res_inv_1 ab_ sh2).
  {
    replace Frame with [field_at_ Tsh (Tstruct _ab noattr) [StructField _join] ab_;
                        field_at_ Tsh (Tstruct _ab noattr) [StructField _a] ab_;
                        field_at_ Tsh (Tstruct _ab noattr) [StructField _b] ab_] by (unfold Frame; reflexivity).
    simpl. entailer. cancel.
    unfold data_at_, field_at_, field_at.
    normalize.
    apply andp_right.
      apply prop_right; intuition.
        now apply field_compatible_tlock; auto.
        now apply default_value_fits.
      
      now apply derives_refl.
  }
  {
    intuition.
    - (* precise R *)
      admit.
    - (* positive R *)
      admit.
  }
  
  (* COMMAND: makelock(); *)
  (* establish the lock invariant *)
  (* split the frame to extract the lock *)
  normalize.
  name ab _ab__1.
  forward_call_threadlib (field_address (Tstruct _ab noattr) [StructField _join] ab_, Tsh) (res_inv_2 ab_ sh2).
  {
    apply prop_right; f_equal.
    unfold field_address.
    if_tac; [reflexivity|tauto].
  }
  {
    replace Frame with [lock_inv Tsh ab_ (res_inv_1 ab_ sh2);
                        field_at_ Tsh (Tstruct _ab noattr) [StructField _a] ab_;
                        field_at_ Tsh (Tstruct _ab noattr) [StructField _b] ab_] by (unfold Frame; reflexivity).
    simpl.
    entailer.
    cancel.
    unfold data_at_, field_at_, field_at.
    normalize.
    apply andp_right. apply prop_right; intuition.
      now apply field_compatible_tlock_join; auto.
      now apply default_value_fits.
      assert_PROP (isptr ab_) as I1 by entailer.
      assert_PROP (isptr (field_address (Tstruct _ab noattr) [StructField _join] ab_)) as I2 by entailer.
      apply derives_refl'.
      unfold at_offset, offset_val.
      f_equal.
      destruct (field_address (Tstruct _ab noattr) [StructField _join] ab_) eqn : E2; try inversion I2.
      destruct (ab_) eqn : E1; try inversion I1.
      clear -E2.
      unfold field_address, nested_field_offset2, nested_field_rec, field_offset, fieldlist.field_offset2, Ctypes.field_offset in *; simpl in *.
      if_tac in E2; inversion E2.
      rewrite Int.add_zero; auto.
  }
  {
    intuition.
    - (* precise R *)
      admit.
    - (* positive R *)
      admit.
  }
  
  (* COMMAND: ab->a = 1; *)
  normalize.
  forward.
  
  (* COMMAND: ab->b = 2; *)
  forward.
  
  (* release part of the join lock *)
  rewrite <- (lock_inv_share_join _ _ _ _ _ Join).
  normalize.
  
  (* COMMAND: release(); *)
  forward_call_threadlib (ab_, Tsh) (res_inv_1 ab_ sh2).
  {
    (* specify the passed frame evar generated by forward_call to be [ab->lock |-> l_] *)
    replace Frame with [lock_inv sh1 (field_address (Tstruct _ab noattr) [StructField _join] ab_) (res_inv_2 ab_ sh2)] by (unfold Frame; reflexivity).
    simpl; cancel.
    unfold res_inv_1.
    rewrite res_invariant_eq.
    unfold data_resource at 1.
    unfold res_inv_2.
    Exists 1.
    match goal with [ |- _ |-- ?F1 * ?F2 * lock_inv sh2 ?p (|> ?R) ] =>
    apply derives_trans with (F1 * F2 * lock_inv sh2 p R)
    end; cancel.
    apply lock_inv_later.
  }
  (* END OF COMMAND: release(); *)
  
  (* COMMAND: spawn_thread(&f, (void* )ab); *)
  
  (* get function specification *)
  get_global_function'' _f.
  normalize.
  apply extract_exists_pre; intros f_.
  match goal with [ |- context[func_ptr' ?P _] ] => abbreviate P as fspec end.
  
  (* build the spawned frame *)
  rewrite <- (lock_inv_share_join _ _ _ _ _ Join).
  pose (spawned_precondition := fun y : val =>
    EX sh : share, !!readable_share sh && lock_inv sh y (res_inv_1 y sh)).
  
  normalize.
  forward_call_threadlib (f_, ab_) spawned_precondition.
  (* in forward we might invoque a theorem saying that if we can call
     spawn with an equivalent (or refined) specification this seems
     too specialize, we could try to see a way around this *)
  {
    (* extract_trivial_liftx *)
    (* renormalize. *)
    rewrite (* exp_fun_comm, *) exp_lift_comm.
    repeat constructor.
  }
  {
    (* the second argument indeed evaluates to ab_ *)
    apply prop_right.
    destruct ab; inversion TC; reflexivity.
  }
  {
    simpl; cancel.
    (* the argument of the global function _f is _args // eventually, an application of the alpha-conversion theorem *)
    do 2 rewrite exp_sepcon1.
    apply @exp_right with _args.
    match goal with [ |- _ |-- func_ptr' ?P _ * _ * _ ] => abbreviate P as fspec_spawned end.
    
    (* specify the frame that stays *)
    replace Frame with [lock_inv sh1 ab_ (res_inv_1 ab_ sh2);
                        lock_inv sh1 (field_address (Tstruct _ab noattr) [StructField _join] ab_)
                                 (res_inv_2 ab_ sh2)] by (unfold Frame; reflexivity); subst Frame.
    (* field_at sh1 (Tstruct _ab noattr) [StructField _lock] (force_val (sem_cast_neutral l_)) ab_] : list mpred)) *)
    simpl.
    unfold spawned_precondition.
    cancel.
    apply exp_right with sh2; entailer.
  }
  
  normalize.
  replace_SEP 0 (`emp).  admit. (* there is some predicate over the heap that I don't know how to handle *)
  
  (* COMMAND: aquire() *)
  assert_PROP (isptr ab_).
  apply derives_trans with (!!isptr ab_ * `(lock_inv sh1 (field_address (Tstruct _ab noattr) [StructField _join] ab_) (res_inv_2 ab_ sh2))).
    entailer. cancel. apply lock_inv_isptr. entailer.
  forward_call_threadlib (field_address (Tstruct _ab noattr) [StructField _join] ab_, sh1) (res_inv_2 ab_ sh2).
  {
    apply prop_right; f_equal.
    unfold field_address, nested_field_offset2, nested_field_rec, field_offset, fieldlist.field_offset2, Ctypes.field_offset; simpl.
    if_tac; tauto.
  }
  
  (* Now that we have acquired back all the lock resources, we put back sh1 and sh2 into Tsh *)
  rewrite res_inv_2_1.
  normalize.
  rewrite <- res_inv_2_1.
  replace_SEP 3 (`(lock_inv sh1 ab_ (|> res_inv_1 ab_ sh2))).
  { entailer; apply lock_inv_later. }
  gather_SEP 1 3.
  replace_SEP 0 (`(lock_inv Tsh ab_ (|> res_inv_1 ab_ sh2))).
  { rewrite <- (lock_inv_share_join _ _ _ _ _ Join).
    entailer. cancel. }
  
  (*
  unfold res_inv_2 at 2.
  rewrite join_res_invariant_eq.
  normalize.
  replace_SEP 4 (`(lock_inv sh1 ab_ (|> res_inv_1 ab_ sh2))).
  { entailer; apply lock_inv_later. }
  gather_SEP 4 1.
  replace_SEP 0 (`(lock_inv Tsh ab_ (|> res_inv_1 ab_ sh2))).
  { rewrite <- (lock_inv_share_join _ _ _ _ _ Join).
    unfold res_inv_1.
    entailer. }
  replace_SEP 3 (`(lock_inv sh1 (field_address (Tstruct _ab noattr) [StructField _join] ab_) (|> res_inv_2 ab_ sh2))).
  { entailer; apply lock_inv_later. }
  gather_SEP 3 2.
  replace_SEP 0 (`(lock_inv Tsh (field_address (Tstruct _ab noattr) [StructField _join] ab_) (|> res_inv_2 ab_ sh2))).
  { rewrite <- (lock_inv_share_join _ _ _ _ _ Join).
    unfold res_inv_1.
    entailer. }
  *)
  
  (* COMMAND: freelock(&ab->lock); *)
  forward_call_threadlib (ab_, Tsh) (res_inv_1 ab_ sh2).
  {
    replace Frame with [lock_inv sh1 (field_address (Tstruct _ab noattr) [StructField _join] ab_)
      (|>res_inv_2 ab_ sh2)] by (unfold Frame; reflexivity).
    simpl fold_right.
    cancel.
    match goal with [ |- _ |-- ?F1 * lock_inv sh1 ?p (|> ?R) ] =>
    apply derives_trans with (F1 *lock_inv sh1 p R)
    end; cancel; [ | apply lock_inv_later ].
    
    admit (* TODO : is it safe to have {R * l []-> |>R} freelock l {R * mapsto .. l} in the logic ? *).
  }
  
  normalize.
  
  (* COMMAND: freelock(&ab->join); *)
  (*  *)
  forward_call_threadlib (field_address (Tstruct _ab noattr) [StructField _join] ab_, Tsh) (res_inv_2 ab_ sh2).
  {
    rewrite res_inv_2_1.
    replace Frame with (@nil mpred) by (unfold Frame; reflexivity).
    simpl.
    cancel.
    entailer.
    (* TODO ENTAILER AND NORMALIZE SOLVE THE GOAL BUT THEY SHOULD NOT BE ABLE TO *)
  }
  normalize.
  
  (* COMMAND: return 0; *)
  forward.
Qed.

Lemma body_f : semax_body Vprog Gprog f_f f_spec.
Proof.
  start_function.
  normalize; intros sh.
  normalize.
  forward.
  assert_PROP (isptr args_).
  stop here
  
  eapply derives_trans; [ | apply lock_inv_isptr ]; entailer.
  forward_call_threadlib (args_, sh) (lock_resource args_).
  {
    destruct _id0; inversion H0; simpl.
    rewrite int_add_repr_0_r; entailer.
  }
  normalize.
  
  unfold lock_resource at 2.
  normalize; intros n.
  normalize.
  forward.
  
  forward.
  
  forward VAR; subst VAR.
  
  forward.
  
  forward_call_threadlib (args_, sh) (lock_resource args_).
  {
    replace Frame with (@nil mpred) by (unfold Frame; reflexivity).
    unfold lock_resource.
    simpl; cancel.
    apply exp_right with (n + 1).
    cancel.
    apply derives_refl'; repeat f_equal.
    destruct n; simpl; auto.
  }
  
  forward_call_threadlib tt tt.
  {
    replace Frame with (@nil mpred) by (unfold Frame; reflexivity).
    (* ??? *)
    admit.
  }
  
  forward.
Qed.
