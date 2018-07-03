Require Import VST.concurrency.common.core_semantics.
Require Import VST.sepcomp.semantics_lemmas.
Require Import VST.sepcomp.mem_lemmas.
Require Import VST.veric.base.
Require Import VST.veric.Clight_core.

Lemma alloc_variables_mem_step: forall cenv vars m e e2 m'
      (M: alloc_variables cenv e m vars e2 m'), mem_step m m'.
Proof. intros.
  induction M.
  apply mem_step_refl.
  eapply core_semantics.mem_step_trans.
    eapply core_semantics.mem_step_alloc; eassumption. eassumption.
Qed.

Lemma assign_loc_mem_step g t m b z v m' (A:assign_loc g t m b z v m'):
    mem_step m m'.
Proof.
  inv A.
  { simpl in H0. eapply mem_step_storebytes. eapply Mem.store_storebytes; eauto. }
  { eapply mem_step_storebytes; eauto. }
Qed.

Lemma bind_parameters_mem_step: forall cenv e m pars vargs m'
      (M: bind_parameters cenv e m pars vargs m'), core_semantics.mem_step m m'.
Proof. intros.
  induction M.
  apply mem_step_refl.
  inv H0.
+ eapply core_semantics.mem_step_trans; try eassumption. simpl in H2.
  eapply mem_step_store; eassumption.
+ eapply core_semantics.mem_step_trans; try eassumption.
  eapply core_semantics.mem_step_storebytes; eassumption.
Qed.

Lemma CLC_corestep_mem:
  forall (g : genv) c (m : mem) c'  (m' : mem),
    core_semantics.corestep (cl_core_sem g) c m c' m' ->
    core_semantics.mem_step m m'.
Proof. simpl; intros. inv H; simpl in *. unfold step2 in H0.
  remember (set_mem c' m') as C'. remember (set_mem c m) as C.
  generalize dependent m'. generalize dependent c'. 
  generalize dependent m. generalize dependent c. 
  induction H0; unfold set_mem; simpl; intros;
  symmetry in HeqC; symmetry in HeqC';
    destruct c; inv HeqC; destruct c'; inv HeqC'; try solve [apply mem_step_refl].
  { eapply assign_loc_mem_step; eauto. }
  { simpl in H1. admit. (* Events.external_call mem_step. ??*) }
  { eapply mem_step_freelist; eauto. }
  { eapply mem_step_freelist; eauto. }
  { eapply mem_step_freelist; eauto. }
  { inv H. eapply alloc_variables_mem_step; eauto. }
  { inv H1. }
Admitted.


Program Definition CLC_memsem  (ge : Clight.genv) :
  @MemSem state.
apply Build_MemSem with (csem := cl_core_sem ge).
eapply CLC_corestep_mem.
Defined.


(*
Lemma assign_loc_forward:
      forall cenv t m b ofs v m'
      (A: assign_loc cenv t m b ofs v m'),
      mem_forward m m'.
Proof.
intros.
induction A.
 unfold Mem.storev in H0.
 eapply store_forward; eassumption.
 eapply storebytes_forward; eassumption.
Qed.

Lemma alloc_variables_forward: forall cenv vars m e e2 m'
      (M: alloc_variables cenv e m vars e2 m'),
      mem_forward m m'.
Proof. intros.
  induction M.
  apply mem_forward_refl.
  apply alloc_forward in H.
  eapply mem_forward_trans; eassumption.
Qed.

Lemma cln_forward: forall (g : genv) (c : corestate)
  (m : mem) (c' : corestate) (m' : mem),
  corestep cl_core_sem g c m c' m' -> mem_forward m m'.
Proof.
intros.
induction H; try apply mem_forward_refl; trivial.
  eapply assign_loc_forward; eassumption.
  eapply alloc_variables_forward; eassumption.
  eapply freelist_forward; eassumption.
Qed.
Program Definition CLN_coop_sem :
  CoopCoreSem Clight.genv (*(Genv.t fundef type)*) corestate.
apply Build_CoopCoreSem with (coopsem := cl_core_sem).
apply cln_forward.
admit. (*This is the new readonly condition which should be easy to prove.*)
Admitted.
*)
