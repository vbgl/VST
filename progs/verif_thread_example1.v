Require Import floyd.proofauto.
Load thread_example1.



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

Definition default_val_lock : reptype tlock := ([Vundef; Vundef;
Vundef; Vundef; Vundef; Vundef; Vundef; Vundef], [Vundef; Vundef;
Vundef; Vundef]).

Axiom lock_inv : share -> val -> mpred -> mpred.

Axiom lock_inv_share_join : forall sh1 sh2 sh v R, sepalg.join sh1 sh2 sh ->
  lock_inv sh1 v R * lock_inv sh2 v R = lock_inv sh v R.

Axiom lock_inv_isptr : forall sh v R, `(lock_inv sh v R) |-- !!(isptr v).

Definition makelock_spec R :=
   WITH v : val, sh : share
   PRE [ _lock OF tptr tlock ]
     PROP (writable_share sh)
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

Definition lock_resource p :=
  EX n : Z,
     field_at Tsh (Tstruct _ab noattr) [StructField _a] (Vint (Int.repr n)) p *
     field_at Tsh (Tstruct _ab noattr) [StructField _b] (Vint (Int.repr (2 * n))) p.

Definition f_spec :=
 DECLARE _f
  WITH args_ : val
  PRE [ _args OF tptr tvoid ]
     PROP ()
     LOCAL (temp _args args_)
     SEP (`(EX sh : share, !!(readable_share sh) && lock_inv sh args_ (lock_resource args_)))
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

Lemma body_main : semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  
  (* COMMAND: ab = malloc(..) *)
  (* when forward_call fails, be sure to check that the type of your
  specification matches exactly the type of the function, for example
  here I copy-pasted a specification for mallocN found in verif_queue
  that used tint instead of tuint for the regular malloc *)
  forward_call 32%Z ab_.
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
  
  (* COMMAND: makelock(); *)
  (* establish the lock invariant *)
  (* split the frame to extract the lock *)
  unfold field_at_.
  unfold_field_at 1%nat.
  fold _a _b _lock.
  fold_field_at_.
  forward_call_threadlib (ab_, Tsh) (lock_resource ab_).
  {
    replace Frame with [field_at_ Tsh (Tstruct _ab noattr) [StructField _a] ab_;
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
  simpl.
  
  (* COMMAND: ab->a = 1; *)
  forward.
  rewrite <- field_at_offset_zero.

  (* COMMAND: ab->b = 2; *)
  forward.
  rewrite <- field_at_offset_zero.
  
  (* COMMAND: release(); *)
  forward_call_threadlib (ab_, Tsh) (lock_resource ab_).
  {
    (* specify the passed frame evar generated by forward_call to be [ab->lock |-> l_] *)
    replace Frame with (@nil mpred) by (unfold Frame; reflexivity).
    simpl; cancel.
    unfold lock_resource.
    apply exp_right with 1.
    cancel.
  }
  (* END OF COMMAND: release(); *)
  
  (* COMMAND: spawn_thread(&f, (void* )ab); *)
  
  (* get function specification *)
  get_global_function'' _f.
  normalize.
  apply extract_exists_pre; intros f_.
  match goal with [ |- context[func_ptr' ?P _] ] => abbreviate P as fspec end.
  
  (* build the spawned frame *)
  destruct split_Tsh as (sh1 & sh2 & Rsh1 & Rsh2 & Join).
  rewrite <- (lock_inv_share_join _ _ _ _ _ Join).
  pose (spawned_precondition := fun y : val =>
    EX sh : share, !!readable_share sh && lock_inv sh y (lock_resource y)).
  
  normalize.

eapply semax_seq'.  
  let Frame := fresh "Frame" in
 evar (Frame: list (mpred));
 eapply (semax_call_id00_wow_threadlib (f_, ab_) spawned_precondition Frame).
  reflexivity. reflexivity.
  unfold spawn_thread_spec; simpl.

  reflexivity . reflexivity
 . prove_local2ptree . repeat constructor 
 . try apply local_True_right; entailer!
 . reflexivity
 . prove_local2ptree .
   repeat constructor 
 . reflexivity . reflexivity
 . Forall_pTree_from_elements
 . Forall_pTree_from_elements
 . unfold fold_right at 1 2; cancel
 . cbv beta iota; 
    repeat rewrite exp_uncurry;
    try rewrite no_post_exists0; 
    first [reflexivity . extensionality; simpl; reflexivity]
 . intros; try match goal with  .- extract_trivial_liftx ?A _ =>
        (has_evar A; fail 1) || (repeat constructor)
     end
 | unify_postcondition_exps
 | unfold fold_right_and; repeat rewrite and_True; auto
 ].




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
    destruct _id; inversion TC; reflexivity.
  }
  {
    simpl; cancel.
    (* the argument of the global function _f is _args // eventually, an application of the alpha-conversion theorem *)
    do 2 rewrite exp_sepcon1.
    apply @exp_right with _args.
    match goal with [ |- _ |-- func_ptr' ?P _ * _ * _ ] => abbreviate P as fspec_spawned end.
    
    (* specify the frame that stays *)
    replace Frame with [lock_inv sh1 ab_ (lock_resource ab_)] by (unfold Frame; reflexivity); subst Frame.
    (* field_at sh1 (Tstruct _ab noattr) [StructField _lock] (force_val (sem_cast_neutral l_)) ab_] : list mpred)) *)
    simpl.
    unfold spawned_precondition.
    cancel.
    apply exp_right with sh2; entailer.
  }
  
  normalize.
  replace_SEP 0 (`emp).  admit. (* there is some predicate over the heap that I don't know how to handle *)
  
  (* COMMAND: aquire() *)
  assert_PROP (isptr ab_). eapply derives_trans; [ | apply lock_inv_isptr ]. entailer.
  forward_call_threadlib (ab_, sh1) (lock_resource ab_).
  
  (* COMMAND: a=ab->a *)
  normalize.
  unfold lock_resource at 2.
  normalize; intros n.
  flatten_sepcon_in_SEP.
  forward.
  
  (* COMMAND: while loop *)
  drop_LOCAL 1%nat.
  pose (loop_inv := @exp (environ -> mpred) _ _ (fun n : Z =>
    PROP ()
    LOCAL (temp _a (Vint (Int.repr n)); temp _ab__1 ab_)
    SEP (
      `(field_at Tsh (Tstruct _ab noattr) [StructField _a] (Vint (Int.repr n)) ab_) ;
      `(field_at Tsh (Tstruct _ab noattr) [StructField _b] (Vint (Int.repr (2 * n))) ab_) ;
      `(lock_inv sh1 ab_ (lock_resource ab_))
    )
  )).
  forward_while loop_inv a_.
  now apply exp_right with n; entailer (* precondition => loop invariant *).
  now apply prop_right, I (* loop condition is well-behaved *).
  {
    (* loop body *)
    
    (* COMMAND: release() *)
    forward_call_threadlib (ab_, sh1) (lock_resource ab_).
    {
      replace Frame with (@nil mpred) by (unfold Frame; reflexivity).
      simpl fold_right.
      unfold lock_resource.
      cancel.
      apply exp_right with a_.
      cancel.
    }
    
    (* COMMAND: acquire() *)
    forward_call_threadlib (ab_, sh1) (lock_resource ab_).
    
    (* COMMAND: a = ab->a; *)
    unfold lock_resource at 2.
    clear n; normalize; intros n.
    flatten_sepcon_in_SEP.
    forward VAR; subst VAR.
    
    (* back to loop invariant *)
    apply exp_right with n.
    entailer.
  }
  (* after the loop *)
  
  (* COMMAND: b = ab->b; *)
  forward.
  
  (* COMMAND: freelock(&ab->lock); *)
  forward_call_threadlib (ab_, Tsh) (lock_resource ab_).
  {
    replace Frame with (@nil mpred) by (unfold Frame; reflexivity).
    simpl fold_right.
    unfold lock_resource at 2.
    normalize.
    apply exp_right with a_.
    cancel.
    (* HERE we cannot free the lock because we need total ownership.
    To solve this, we must add "lock_inv sh2" to the lock invariant *)
    admit.
  }
  normalize.
  
  (* COMMAND: return(b); *)
  forward.
Qed.

Lemma body_f : semax_body Vprog Gprog f_f f_spec.
Proof.
  start_function.
  normalize; intros sh.
  normalize.
  forward.
  assert_PROP (isptr args_). eapply derives_trans; [ | apply lock_inv_isptr ]; entailer.
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
