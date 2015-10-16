(** Usage of this file:

(* After the Instance CompSpecs and requiring your program file, which
   should load the primitives from threads.h, load the names into this
   module: *)

Module threadlib_args <: threadlib_args.
  Let CompSpecs := CompSpecs.
  Let _lock := _lock.
  Let _lock_t := _lock_t.
  Let _f := _f.
  Let _args := _args.
  Let _makelock := _makelock.
  Let _freelock := _freelock.
  Let _acquire := _acquire.
  Let _release := _release.
  Let _spawn_thread := _spawn_thread.
  Let _exit_thread := _exit_thread.
End threadlib_args.

(* then load the library: *)

Module threadlib := threadlib threadlib_args.
Import threadlib.

(* then use the following tactic when calling a thread function, where
   args corresponds to its WITH clause and R is the predicate specific
   to the thread function *)

forward_call_threadlib args R.

*)

Require Import floyd.proofauto.

Module Type threadlib_args.
  Parameter CompSpecs : compspecs.
  (* these are all names defined in threads.h. They might not appear
  in the file, in which case, choose a fresh identifier *)
  Parameters
    _lock (* anonymous *)
    _lock_t
    _f (* anonymous *)
    _args (* anonymous *)
    _makelock
    _freelock
    _acquire
    _release
    _spawn_thread
    _exit_thread : ident.
End threadlib_args.

Module threadlib (args : threadlib_args).
Import args.

Local Open Scope logic.

Definition tlock := Tstruct _lock_t noattr.

Axiom lock_inv : share -> val -> mpred -> mpred.

Axiom lock_inv_share_join : forall sh1 sh2 sh v R, sepalg.join sh1 sh2 sh ->
  lock_inv sh1 v R * lock_inv sh2 v R = lock_inv sh v R.

Axiom lock_inv_isptr : forall sh v R, `(lock_inv sh v R) |-- !!(isptr v).

Definition makelock_spec R :=
   WITH v : val, sh : share
   PRE [ _lock OF tptr tlock ]
     PROP (writable_share sh)
     LOCAL (temp _lock v)
     SEP (`(data_at_ sh tlock v))
   POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (`(lock_inv sh v R)).

Definition freelock_spec R :=
   WITH v : val, sh : share
   PRE [ _lock OF tptr tlock ]
     PROP (writable_share sh)
     LOCAL (temp _lock v)
     SEP (`R ; `(lock_inv sh v R))
   POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (`R ; `(data_at_ sh tlock v)).

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

End threadlib.