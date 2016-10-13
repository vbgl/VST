Require Import Events.
Require Import Memory.
Require Import Coqlib.
Require Import Values.
Require Import Maps.
Require Import Integers.
Require Import AST.
Require Import Globalenvs.
Require Import Axioms.

Require Import sepcomp.mem_lemmas. (*needed for definition of mem_forward etc*)
Require Import sepcomp.semantics.
Require Import sepcomp.semantics_lemmas.
(*
Require Import structured_injections.
Require Import reach.*)
Require Import sepcomp.effect_semantics.

Require Import msl.Axioms. (*for extensionality*)

Require Import minisepcomp.mini_simulations.
Require Import minisepcomp.mini_simulations_lemmas.
Require Import Wellfounded.
Require Import Relations.
Require Import minisepcomp.mini_diagram_trans.
Require Import minisepcomp.interpolation_memory.
Require Import minisepcomp.mini_interpolation.
(*Require Import interpolants.
Require Import interpolation_proofs.

Require Import full_composition.
*)
Require Import minisepcomp.BuiltinEffects.

(** * Transitivity of Structured Simulations *)

(*Module EFFAX : EffectInterpolationAxioms := EffectInterpolations.*)

Import Mini_simulation_inj.

(*
Lemma empty_inj: Mem.inject (Mem.flat_inj 1%positive) Mem.empty Mem.empty.
Proof.
  split.
    split. intros. destruct (flatinj_E _ _ _ _ H) as [? [? ?]]. subst.
          rewrite Zplus_0_r. assumption.
       intros. destruct (flatinj_E _ _ _ _ H) as [? [? ?]]. subst.
          apply Z.divide_0_r.
    intros. destruct (flatinj_E _ _ _ _ H) as [? [? ?]]. subst.
         exfalso. xomega.
     intros. unfold Mem.flat_inj.
          remember (plt b 1).
          destruct s; trivial. xomega.
    intros. destruct (flatinj_E _ _ _ _ H) as [? [? ?]]. subst.
         exfalso. xomega.
    intros b; intros.
      destruct (flatinj_E _ _ _ _ H0) as [? [? ?]]. subst.
         exfalso. xomega.
    intros.
      destruct (flatinj_E _ _ _ _ H) as [? [? ?]]. subst.
         exfalso. xomega.
 (*spill*)
  intros. apply flatinj_E in H. destruct H as [? [? ?]]; subst. rewrite Zplus_0_r in H0.
  left; trivial.
Qed.

Lemma empty_fwd: forall m, mem_forward Mem.empty m.
Proof. intros m b Vb.
   unfold Mem.valid_block in Vb. simpl in Vb. exfalso. xomega.
Qed.
*)

Lemma initial_inject_split: forall j m1 m3 (Inj:Mem.inject j m1 m3),
  exists m2 j1 j2, j = compose_meminj j1 j2 /\
       Mem.inject j1 m1 m2 /\ Mem.inject j2 m2 m3 /\
       (forall b1, (exists b3 d, compose_meminj j1 j2 b1 = Some(b3,d))
                   <-> (exists b2 d1, j1 b1 = Some(b2,d1))) /\
       (forall b2 b3 d2, j2 b2 =Some(b3,d2) ->
                   exists b1 d, compose_meminj j1 j2 b1 = Some(b3,d)) /\
      (forall b1 b2 ofs2, j1 b1 = Some(b2,ofs2) -> (b1=b2 /\ ofs2=0)) /\
      (forall b2 b3 ofs3, j2 b2 = Some (b3, ofs3) ->
               Mem.flat_inj 1%positive b2 = Some (b3, ofs3) \/
               (b2 = Mem.nextblock Mem.empty /\
                    compose_meminj j1 j2 (Mem.nextblock Mem.empty) = Some (b3, ofs3)) \/
               (exists m : positive,
                   b2 = (Mem.nextblock Mem.empty + m)%positive /\
                   compose_meminj j1 j2 (Mem.nextblock Mem.empty + m)%positive =
                   Some (b3, ofs3))) (*/\ pure_composition j1 j2 m1 m2*).
Proof. 
  intros. 
  rename j into l.
  (* The constructions *)
  remember (filter_id l) as j;
  remember l as k;
  remember m1 as m2.
  
  (*The proof *)
  exists m2, j, k.
  split.
  { subst. unfold compose_meminj, filter_id.
    extensionality b.
    destruct (l b) eqn:lmap; trivial.
    rewrite lmap. destruct p; auto. }
  split.
  (*Mem.inject j m2 m2*) (* this uses the hyp Inj *)
  {constructor.
   + { constructor.
       + subst; intros.
         unfold filter_id in H; destruct (l b1); try solve [inversion H].
         inversion H; subst. replace (ofs + 0) with ofs by omega.
         auto.
       + subst; intros.
         unfold filter_id in H; destruct (l b1); try solve [inversion H].
         inversion H; subst. unfold Pos.divide; exists 0; omega. 
       + subst k j; intros.
         unfold filter_id in H; destruct (l b1) eqn:lmap; try solve [inversion H].
         inversion H; subst b1 delta. replace (ofs + 0) with ofs by omega.
         subst m2; clear H. destruct (ZMap.get ofs (Mem.mem_contents m1) !! b2) eqn:cont; try constructor.
         (*TRY*)
         destruct Inj. destruct mi_inj.
         destruct p; eapply mi_memval in lmap; eauto.
         rewrite cont in lmap. inv lmap. rename v2 into v3. 
         unfold filter_id. inv H1; try constructor.
         econstructor. rewrite H; reflexivity.
         rewrite Int.add_unsigned.
         rewrite Int.unsigned_repr_eq.
         rewrite Zmod_0_l. replace (Int.unsigned ofs1 + 0) with (Int.unsigned ofs1) by omega.
         symmetry; apply Int.repr_unsigned. }
   + subst; intros. apply Inj in H. 
     unfold filter_id. rewrite H; auto.
   + subst; intros. destruct Inj.
     destruct (valid_block_dec m1 b'); trivial.
     apply mi_freeblocks in n. 
     unfold filter_id in H; destruct (l b) eqn:lmap; try solve [inversion H].
     inversion H; subst. rewrite n in lmap; inversion lmap.
   + subst; intros.
     unfold Mem.meminj_no_overlap, filter_id. intros.
     destruct (l b1); inversion H0.
     destruct (l b2); inversion H1.
     subst. left; exact H.
   + subst; intros. unfold filter_id in H. destruct (l b) eqn: lmap; inversion H.
     subst. split; try omega. replace (Int.unsigned ofs + 0) with (Int.unsigned ofs) by omega.
     apply Int.unsigned_range_2.
   + (*spill*) intros.
     unfold filter_id in Heqj; subst j. remember (k b1). destruct o; inv H.
     rewrite Zplus_0_r in H0. left; trivial.
   }
  split.
  (*Mem.inject k m2 m3*)
  { exact Inj. }
  split.
  {intros; subst. unfold compose_meminj, filter_id. 
   destruct (l b1) eqn:lmap. 
   + rewrite lmap. destruct p. split; intros.
     - exists b1, 0; reflexivity.
     - exists b, (0 + z); reflexivity.
   + split; intros H; destruct H as [b3 [d H]]; inversion H.
  }
  split.
  { intros. subst. unfold compose_meminj, filter_id. 
    exists b2, d2; rewrite H, H. f_equal; omega. }
  split.
  { subst; intros.
    unfold filter_id in H; destruct (l b1); try solve [inversion H].
    inversion H; subst. auto. }
  { intros; subst. 
    unfold Mem.empty in *; simpl in *.
    destruct (Pcompare b2 1%positive Eq) eqn:eqn.
    + subst. destruct b2; try solve[inversion eqn].
      right; left; split; auto; subst.
      unfold compose_meminj, filter_id. rewrite H, H. f_equal; omega.
    + destruct b2; inversion eqn. (*Impossible: b2 < 1 *)
    + assert (Gtb: Pgt b2 1) by apply eqn.
      right; right.
      apply Pos.gt_iff_add in Gtb. destruct Gtb as [m b2eq].
      exists m. split. 
      - subst; auto.
      - simpl in b2eq. rewrite b2eq.
        unfold compose_meminj, filter_id.
        rewrite H, H. f_equal; omega. }
Qed.
(*
Lemma compose_sm_sharedSrc mu12 mu23: forall
     (HP: forall b, pubBlocksTgt mu12 b = true -> pubBlocksSrc mu23 b = true)
     (HF: forall b, frgnBlocksTgt mu12 b = true -> frgnBlocksSrc mu23 b = true)
     (WD12: SM_wd mu12) (WD23: SM_wd mu23),
  sharedSrc (compose_sm mu12 mu23) = sharedSrc mu12.
Proof. intros. 
  rewrite (sharedSrc_iff_frgnpub mu12); trivial.
  rewrite (sharedSrc_iff_frgnpub (compose_sm mu12 mu23)).
     trivial.
  eapply compose_sm_wd; eassumption.
Qed.
 
Lemma compose_sm_exportedSrc mu12 mu23 vals: forall
     (HP: forall b, pubBlocksTgt mu12 b = true -> pubBlocksSrc mu23 b = true)
     (HF: forall b, frgnBlocksTgt mu12 b = true -> frgnBlocksSrc mu23 b = true)
     (WD12: SM_wd mu12) (WD23: SM_wd mu23),
  exportedSrc (compose_sm mu12 mu23) vals = exportedSrc mu12 vals.
Proof. intros. unfold exportedSrc.  
  rewrite compose_sm_sharedSrc; trivial. 
Qed. 

Lemma compose_sm_sharedTgt mu12 mu23:
  sharedTgt (compose_sm mu12 mu23) = sharedTgt mu23.
Proof. intros. reflexivity. Qed.

Lemma compose_sm_exportedTgt mu12 mu23 vals:
  exportedTgt (compose_sm mu12 mu23) vals = exportedTgt mu23 vals.
Proof. intros. reflexivity. Qed.
*)

(** ** Transitivity Proper *)

Section Eff_sim_trans.
Context {F1 V1 C1 F2 V2 C2 F3 V3 C3:Type}
        (Sem1 : @EffectSem (Genv.t F1 V1) C1)
        (Sem2 : @EffectSem (Genv.t F2 V2) C2)
        (Sem3 : @EffectSem (Genv.t F3 V3) C3)
        (g1 : Genv.t F1 V1)
        (g2 : Genv.t F2 V2)
        (g3 : Genv.t F3 V3).

Lemma load_store_init_data_inject m1 m2 j1 
       (J: forall b, isGlobalBlock g1 b = true -> j1 b = Some(b,0))
       (PG1 : meminj_preserves_globals g1 j1) 
       (Inj12 : Mem.inject j1 m1 m2)
       (FindVars: forall i b, Genv.find_symbol g1 i = Some b -> Genv.find_symbol g2 i = Some b):
      forall il k b
      (LDI: Genv.load_store_init_data g1 m1 b k il)
      (G: isGlobalBlock g1 b = true),
   Genv.load_store_init_data g2 m2 b k il.
Proof. 
  induction il; simpl in *; intros. trivial.
  assert (Inj: forall ofs v1 chunk, Mem.load chunk m1 b ofs = Some v1 ->
      exists v2 : val,
      Mem.load chunk m2 b ofs = Some v2 /\ val_inject j1 v1 v2).
  { intros. specialize (Mem.load_inject j1 m1 m2 _ _ _ _ _ _ Inj12 H (J _ G)). rewrite Zplus_0_r; trivial. }
  destruct a.
  { destruct LDI; split; eauto.
      destruct (Inj _ _ _ H) as [v [A B]]. inv B; trivial. }
  { destruct LDI; split; eauto.
      destruct (Inj _ _ _ H) as [v [A B]]. inv B; trivial. }
  { destruct LDI; split; eauto.
      destruct (Inj _ _ _ H) as [v [A B]]. inv B; trivial. }
  { destruct LDI; split; eauto.
      destruct (Inj _ _ _ H) as [v [A B]]. inv B; trivial. }
  { destruct LDI; split; eauto.
      destruct (Inj _ _ _ H) as [v [A B]]. inv B; trivial. }
  { destruct LDI; split; eauto.
      destruct (Inj _ _ _ H) as [v [A B]]. inv B; trivial. }
  { destruct LDI as [LDI1 LDI2].
    split. admit. (*HOLE in SEPCOMP -- Genv_read-as_zero preserved m1 to m2 for global blocks?*) 
    apply IHil; assumption. }
  { destruct LDI as [[b' [FS LD]] LSI].
    split; eauto. 
    destruct (Inj _ _ _ LD) as [v [A B]]. inv B.
    rewrite J in H1.
      inv H1. rewrite Int.add_zero in A.
      exists b2; eauto.
    eapply find_symbol_isGlobal; eassumption. } 
Admitted.

Theorem eff_sim_trans: forall 
        (SIM12: @Mini_simulation_inject _ _ _ _ _ _ Sem1 Sem2 g1 g2)
        (SIM23: @Mini_simulation_inject _ _ _ _ _ _ Sem2 Sem3 g2 g3),
        @Mini_simulation_inject _ _ _ _ _ _ Sem1 Sem3 g1 g3.
Proof. 
  intros.
  destruct SIM12
    as [core_data12 match_core12 core_ord12 core_ord_wf12 
      match_wd12 senvs_equiv12 match_genv12
      match_valid12 core_initial12 effcore_diagram12
      core_halted12 core_at_external12 eff_after_external12].  
  destruct SIM23 
    as [core_data23 match_core23 core_ord23 core_ord_wf23 
      match_wd23 senvs_equiv23 match_genv23
      match_valid23 core_initial23 effcore_diagram23
      core_halted23 core_at_external23 eff_after_external23].
  eapply Build_Mini_simulation_inject with
    (core_ord := clos_trans _ (sem_compose_ord_eq_eq core_ord12 core_ord23 C2))
    (match_state := fun d j L1 c1 m1 L3 c3 m3 => 
      match d with (d1,X,d2) => 
        exists c2, exists m2, exists j1, exists j2, exists L2,                                 
          X=Some c2 /\ j = compose_meminj j1 j2 /\ 
          (*(locBlocksTgt mu1 = locBlocksSrc mu2 /\
           extBlocksTgt mu1 = extBlocksSrc mu2 /\
           (forall b, pubBlocksTgt mu1 b = true -> pubBlocksSrc mu2 b = true) /\
           (forall b, frgnBlocksTgt mu1 b = true -> frgnBlocksSrc mu2 b = true)) /\ *)
          match_core12 d1 j1 L1 c1 m1 L2 c2 m2 /\ match_core23 d2 j2 L2 c2 m2 L3 c3 m3 /\
          full_ext j1 j2 L1 L2
      end).
{ (*well_founded*)
  eapply wf_clos_trans. 
  eapply well_founded_sem_compose_ord_eq_eq; assumption. }
{ (*match_wd*) clear - match_wd12 match_wd23.
  intros. rename c2 into c3. rename m2 into m3. rename L2 into L3. rename b2 into b3.
  destruct d as [[d12 cc2] d23].
  destruct MS as [c2 [m2 [j12 [j23 [L2 [X [JJ (*[INV*) [MC12 [MC23 FULL]]]]]]]]]; subst.
  specialize (match_wd12 _ _ _ _ _ _ _ _ MC12).
  specialize (match_wd23 _ _ _ _ _ _ _ _ MC23).
  destruct (compose_meminjD_Some _ _ _ _ _ J) as [b2 [d1 [d2 [J12 [J23 D]]]]]; clear J. subst.
  destruct (match_wd12 _ _ _ J12).
  destruct (match_wd23 _ _ _ J23). eauto. }
{ (*genvs_domain_eq*)
  clear - senvs_equiv12 senvs_equiv23. eapply senv_equiv_trans; eassumption. }
(*{ (* ginfos_preserved *) 
  clear - ginfos_pres12 ginfos_pres23.
  destruct ginfos_pres12 as [GvarInfo12 GfindSymb12].
  destruct ginfos_pres23 as [GvarInfo23 GfindSymb23].
  split; red; intros.
    specialize (GvarInfo12 b). specialize (GvarInfo23 b). unfold gvar_info_eq in *.
    destruct (Genv.find_var_info g1 b); destruct (Genv.find_var_info g3 b); trivial.
    destruct (Genv.find_var_info g2 b); try contradiction. 
    destruct GvarInfo12 as [A [B C]]. rewrite A, B, C. assumption.
    destruct (Genv.find_var_info g2 b); try contradiction.
    destruct (Genv.find_var_info g2 b); try contradiction.
  apply GfindSymb23. apply GfindSymb12. assumption. }*)
{ (*match_genv*)
  clear - match_genv23 senvs_equiv23 match_genv12 senvs_equiv12.
  intros. rename c2 into c3. rename m2 into m3. rename L2 into L3.
  destruct d as [[d12 cc2] d23].
  destruct MC as [c2 [m2 [j12 [j23 [L2 [X [J (*[INV*) [MC12 [MC23 IFDL]]]]]]]]]; subst.
  destruct (match_genv12 _ _ _ _ _ _ _ _ MC12) as [GE12a [GE12b GE12c]].
  destruct (match_genv23 _ _ _ _ _ _ _ _ MC23) as [GE23a [GE23b GE23c]].
  split; [| split].
  + eapply symbols_inject_trans; eauto. 
  + admit. (*apply meminj_preserves_genv2blocks.
         apply meminj_preserves_genv2blocks in GE12b.
         apply meminj_preserves_genv2blocks in GE23b.
         Locate meminj_preserves_globals_ind_compose.
         solve [eapply meminj_preserves_globals_ind_compose; eassumption].*)
  + intros b1 GB N.
    destruct (compose_meminjD_None _ _ _ N). elim (GE12c _ GB H).
    destruct H as [b2 [d [J12 J23]]]. eelim GE23c; try eassumption.
    admit. (*Should be true, even with elimglobals phase*) 
  }
(*{ (*match_reach_closed*)
    clear - match_sm_wd12 match_visible12.
    intros. rename c2 into c3. rename m2 into m3.
    destruct d as [[d12 cc2] d23].
    destruct H as [c2 [m2 [mu12 [mu23 [X [J [INV [MC12 [MC23 IFDL]]]]]]]]]; subst.
    simpl. rewrite vis_compose_sm. eapply match_visible12. eassumption. } *)
{ (*meminj_valid*)
    clear - match_valid12 match_valid23.
    intros. rename c2 into c3. rename m2 into m3. rename L2 into L3.
    destruct d as [[d12 cc2] d23].
    destruct MS as [c2 [m2 [j12 [j23 [L2 [X [J (*[INV*) [MC12 [MC23 IFDL]]]]]]]]]; subst.
    specialize (match_valid12 _ _ _ _ _ _ _ _ MC12).
    specialize (match_valid23 _ _ _ _ _ _ _ _ MC23).
    unfold meminj_valid.
    destruct match_valid12 as [MC12a [MC12b MC12c]].
    destruct match_valid23 as [MC23a [MC23b MC23c]].
    split; intros. eauto.
    split; intros. eauto.
    rename b2 into b3. apply compose_meminjD_Some in J.
    destruct J as [b2 [d1 [d2 [J12 [J23 D]]]]].
    split. eapply MC12c; eauto. eapply MC23c; eauto. }
{ (*initial_core*)
  clear - senvs_equiv12 core_initial12 senvs_equiv23 core_initial23.
   intros. rename m2 into m3. rename vals2 into vals3. 
    (*assert (HT: Forall2 Val.has_type vals1 (sig_args sig)). 
      eapply forall_valinject_hastype; eassumption.*)
    destruct (initial_inject_split _ _ _ H0) 
       as [m2 [j1 [j2 [J [Inj12 [Inj23 [X [Y [XX YY (*Pure*)]]]]]]]]].
    subst.
    destruct (forall_val_inject_split _ _ _ _ H1)
       as [vals2 [ValsInj12 ValsInj23]].
    assert (PG1: meminj_preserves_globals g1 j1).
      clear - X Y XX YY H2 H0 H1.
      apply meminj_preserves_genv2blocks.
      apply meminj_preserves_genv2blocks in H2.
      destruct H2 as [AA [BB CC]].
      split; intros.
         specialize (AA _ H).
         destruct (compose_meminjD_Some _ _ _ _ _ AA)
            as [b2 [d1 [d2 [J1 [J2 D]]]]]; subst; clear AA.
         destruct (XX _ _ _ J1); subst. trivial.
      split; intros.
         specialize (BB _ H).
         destruct (compose_meminjD_Some _ _ _ _ _ BB)
            as [b2 [d1 [d2 [J1 [J2 D]]]]]; subst; clear BB.
         destruct (XX _ _ _ J1); subst. trivial.
      destruct (XX _ _ _ H2); subst. trivial.
  (*assert (GFI1: globalfunction_ptr_inject g1 j1).
    { clear - X Y XX YY H2 H3.
      intros b f Hfind.
      destruct (H3 b f Hfind); split; auto.
      apply compose_meminjD_Some in H. 
      destruct H as [b1 [ofs1 [ofs [U [R S]]]]]. rewrite S.
      rewrite U. apply XX in U. destruct U. subst b ofs1. rewrite <-S. auto. }*)
  assert (PG2: meminj_preserves_globals g2 j2).
  { admit. (*
    clear - XX YY X Y PG1 H2 H0 H1 senvs_equiv12.
    apply meminj_preserves_genv2blocks.
     apply meminj_preserves_genv2blocks in H2.
      destruct H2 as [AA [BB CC]].
     apply meminj_preserves_genv2blocks in PG1.
      destruct PG1 as [AA1 [BB1 CC1]].
      destruct senvs_equiv12.
      split; intros.
         apply H in H3.
         specialize (AA1 _ H3). specialize (AA _ H3).
         destruct (compose_meminjD_Some _ _ _ _ _ AA)
            as [b2 [d1 [d2 [J1 [J2 D]]]]]; subst; clear AA.
         rewrite J1 in AA1. inv AA1. simpl in D. subst. trivial.
      split; intros.
         apply H2 in H3.
         specialize (BB1 _ H3). specialize (BB _ H3).
         destruct (compose_meminjD_Some _ _ _ _ _ BB)
            as [b2 [d1 [d2 [J1 [J2 D]]]]]; subst; clear BB.
         rewrite J1 in BB1. inv BB1. simpl in D. subst. trivial.
      apply H2 in H3.
         specialize (BB1 _ H3). specialize (BB _ H3). rename b2 into b3.
         destruct (compose_meminjD_Some _ _ _ _ _ BB)
            as [b2 [d1 [d2 [J1 [J2 D]]]]]; subst; clear BB.
         destruct (XX _ _ _ J1); subst. simpl in D. subst.
         clear BB1 XX.
         destruct (YY _ _ _ H4) as [XX | [XX | XX]].
           apply flatinj_E in XX. destruct XX as [? [? ?]]; subst. trivial.
           destruct XX as [? ?]; subst.
             apply (CC _ _ _ H3 H6).
           destruct XX as [mm [? ?]]; subst.
             apply (CC _ _ _ H3 H6).*) }
  (*assert (GFI2: globalfunction_ptr_inject g2 j2).
  { clear - XX YY X Y PG1 H2 H3 genvs_dom_eq12 GFI1.
    intros b f Hfind2.
    generalize genvs_dom_eq12 as GDE. intro.
    destruct genvs_dom_eq12 as [U [W R]].
    specialize (R b).
    destruct R.
    assert (exists f, Genv.find_funct_ptr g1 b = Some f).
    { apply H0. eauto. }
    destruct H1 as [f0 Hfind1].
    unfold globalfunction_ptr_inject in H3.
    destruct (H3 b f0 Hfind1); split; auto.
    apply compose_meminjD_Some in H1. 
    destruct H1 as [b1 [ofs1 [ofs [UU [R S]]]]]. rewrite S.
    destruct (GFI1 b f0 Hfind1).
    rewrite H1 in UU.
    inv UU.
    rewrite R.
    f_equal; auto. 
    rewrite <-(genvs_domain_eq_isGlobal _ _ GDE); auto. }*)
(*
  assert (MRR2: mem_respects_readonly g2 m2). 
    { admit. TODO red; intros b gv'; intros.
      (*clear YY H0 H1 H2 H3 H4 H5 core_initial23 core_initial12 X Y.*)
      destruct ginfos_pres12 as [GVars12 FS12].
      destruct ginfos_pres23 as [GVars23 FS23].
      specialize (find_var_info_isGlobal _ _ _ H10); intros GB.
      specialize (meminj_preserves_globals_isGlobalBlock _ _ PG2 _ GB); intros J2b.
      rewrite <- (genvs_domain_eq_isGlobal _ _ genvs_dom_eq12) in GB. 
      specialize (meminj_preserves_globals_isGlobalBlock _ _ PG1 _ GB); intros J1b.
      specialize (GVars12 b); red in GVars12. rewrite H10 in GVars12.
      remember (Genv.find_var_info g1 b) as fvi. symmetry in Heqfvi.
      destruct fvi; inv GVars12; try contradiction.
      destruct H1 as [GVrd GVvol]; rename H0 into GVInit.
      rewrite <- GVrd, <- GVvol, <- GVInit in *.
      destruct (H6 _ _ Heqfvi H11) as [LDinit1 [VB1 NPerm1]].
      split. eapply load_store_init_data_inject; try eassumption.
             intros. eapply meminj_preserves_globals_isGlobalBlock; eassumption.
      split. eapply Mem.valid_block_inject_2; eassumption.
      intros z N. 
      specialize (GVars23 b); red in GVars23. rewrite H10 in GVars23.
      remember (Genv.find_var_info g3 b) as fvi3. symmetry in Heqfvi3.
      destruct fvi3; inv GVars23; try contradiction.
      destruct H1 as [GVrd3 GVvol3]; rename H0 into GVInit3.
      rewrite GVrd, GVvol, GVInit, GVrd3, GVvol3, GVInit3 in *.
      destruct (H7 _ _ Heqfvi3 H11) as [LDinit3 [VB3 NPerm3]].
      eapply (NPerm3 z). exploit (Mem.perm_inject j2); try eassumption. 
      rewrite Zplus_0_r; trivial. }*)

(*  destruct (core_initial12 _ _ _ _ _ vals2 _ 
       DomS (fun b => match j2 b with None => false
                      | Some (b3,d) => DomT b3 end) H Inj12)
     as [d12 [c2 [Ini2 MC12]]]; try assumption.*)
  assert (MRR2: mem_respects_readonly g2 m2). { admit. (*TODO: readonly_inject*) } 
  destruct (core_initial12 _ vals1 _ _ j1 vals2 _ H Inj12 ValsInj12 PG1)
    as [d12 [c2 [Ini2 MC12]]]; trivial. 
  { admit. }
  (*
    { intros. destruct (X b1) as [_ J1Comp]. 
              destruct J1Comp as [b3 [dd COMP]]. exists b2, d; trivial.
              specialize (H4 _ _ _ COMP).
              destruct (compose_meminjD_Some _ _ _ _ _ COMP)
                as [bb2 [dd1 [dd2 [J1 [J2 D]]]]]; subst; clear COMP.
              rewrite J1 in H10; inv H10. rewrite J2. apply H4. }
    { intros.
        assert (Q: forall b,  isGlobalBlock g2 b || getBlocks vals2 b = true ->
                   exists jb d, j2 b = Some (jb, d) /\ 
                           isGlobalBlock g3 jb || getBlocks vals3 jb = true).
          intros b' Hb'. apply orb_true_iff in Hb'. 
          destruct Hb' as [Hb' | Hb'].
            rewrite (meminj_preserves_globals_isGlobalBlock _ _ PG2 _ Hb').
              exists b', 0.
              rewrite (genvs_domain_eq_isGlobal _ _ genvs_dom_eq23) in Hb'.
              rewrite Hb'. intuition.
          destruct (getBlocks_inject _ _ _  ValsInj23 _ Hb') as [bb [ofs [J2 GB2]]].
              exists bb, ofs. intuition.
        destruct (REACH_inject _ _ _ Inj23 
            (fun b' : block => isGlobalBlock g2 b' || getBlocks vals2 b')
            (fun b' : block => isGlobalBlock g3 b' || getBlocks vals3 b')
            Q _ H10) as [b3 [d2 [J2 R3]]].
        rewrite J2.
        destruct (Y _ _ _ J2) as [b1 [d COMP]].
        apply (H4 _ _ _ COMP). }
    { intros b2 Hb2. remember (j2 b2) as d.
        destruct d; inv Hb2; apply eq_sym in Heqd. destruct p.
        eapply Mem.valid_block_inject_1; eassumption. }*)
  (*destruct (core_initial23 _ _ _ _ _ vals3 _ 
        (fun b => match j2 b with None => false | Some (b3,d) => DomT b3 end) DomT Ini2 Inj23)
        as [d23 [c3 [Ini3 MC23]]]; try assumption. *)
  destruct (core_initial23 _ vals2 _ _ j2 vals3 _ Ini2 Inj23 ValsInj23 PG2)
    as [d23 [c3 [Ini3 MC23]]]; trivial. 
  { admit. }
  (*  { intros b2 b3 d2 J2. rewrite J2.
         destruct (Y _ _ _ J2) as [b1 [d COMP]].
         destruct (H4 _ _ _ COMP). split; trivial. }
    { intros b2 Hb2. remember (j2 b2) as d.
        destruct d; inv Hb2; apply eq_sym in Heqd. destruct p.
        eapply Mem.valid_block_inject_1; eassumption. }
  remember (initial_SM DomS
            (fun b : block =>
             match j2 b with
             | Some (b3, _) => DomT b3
             | None => false
             end) (REACH m1 (fun b => isGlobalBlock g1 b || getBlocks vals1 b))
                  (REACH m2 (fun b => isGlobalBlock g2 b || getBlocks vals2 b))
            j1) as mu1.
  remember (initial_SM
            (fun b : block =>
             match j2 b with
             | Some (b3, _) => DomT b3
             | None => false
             end) DomT (REACH m2 (fun b => isGlobalBlock g2 b || getBlocks vals2 b))
                       (REACH m3 (fun b => isGlobalBlock g3 b || getBlocks vals3 b))
             j2) as mu2.*)
  exists (d12,Some c2,d23).
  exists c3. 
  split; trivial. 
  exists c2, m2, j1, j2, (fun b => false). intuition.
  
  (* FULL *)
  { unfold full_ext (*, full_comp, initial_SM*); simpl.
    intros. move X at bottom. 
    assert (H7':exists (b2 : block) (d1 : Z), j1 b1 = Some (b2, d1)) by (exists b2, delta1; auto).
    apply X in H7'.
    destruct H7' as [b3 [delta2 HH]]. split; trivial.
    apply compose_meminjD_Some in HH. destruct HH as [bb2 [dd1 [dd2 [JJ1 [JJ2 DD]]]]].
    rewrite H7 in JJ1; inv JJ1. eexists; eexists; eassumption.
  }
 }
{ (*effcore_diagram*)
   clear - match_wd12 match_valid12 effcore_diagram12 
           match_wd23 match_valid23 effcore_diagram23
           match_genv23.
   intros. rename st2 into st3. rename m2 into m3. rename L2 into L3.
   destruct cd as [[d12 cc2] d23].
   destruct H0 as [c2 [m2 [j12 [j23 [L2 [X [J (*[INV*) [MC12 [MC23 full]]]]]]]]]; subst.
   eapply effcore_diagram_trans; try eassumption.
   intros. apply match_genv23 in H0. split; eapply H0.
} 
{ (*halted*)
  clear - match_wd12 core_halted12 match_wd23 core_halted23.
  intros. rename c2 into c3. rename m2 into m3. rename L2 into L3.  
  destruct cd as [[d12 cc2] d23].
  destruct H as [c2 [m2 [j12 [j23 [L2 [X [J (*[INV*) [MC12 [MC23 full]]]]]]]]]; subst.
  destruct (core_halted12 _ _ _ _ _ _ _ _ _ MC12 H0) as
     [v2 [MInj12 [MRR1 [MRR2 [RValsInject12 HaltedMid]]]]]. 
  destruct (core_halted23 _ _ _ _ _ _ _ _ _ MC23 HaltedMid) as
     [v3 [MInj23 [_ [MRR3 [RValsInject23 HaltedTgt]]]]].
  exists v3.
  assert (WDmu12:= match_wd12 _ _ _ _ _ _ _ _ MC12).
  assert (WDmu23:= match_wd23 _ _ _ _ _ _ _ _ MC23).
(*  destruct INV as [INVa [INVb [INVc INVd]]].*)
  split. (* rewrite compose_sm_as_inj; trivial.*)
           eapply Mem.inject_compose; eassumption.
  split; trivial.
  split. trivial.   
  split. (* rewrite compose_sm_as_inj; trivial.
         rewrite restrict_compose, vis_compose_sm; simpl.*)
         eapply val_inject_compose; try eassumption. (*
         eapply val_inject_incr; try eassumption.
         apply restrict_incr.*)
  assumption. }
{ (*at_external*)
  clear - match_wd12 core_at_external12 match_wd23 core_at_external23.
  intros. rename c2 into c3. rename m2 into m3. rename L2 into L3.
  rename H0 into AtExtSrc. 
  destruct cd as [[d12 cc2] d23]. 
  destruct H as [st2 [m2 [j12 [j23 [L2 [Hst2 [J (*[GLUEINV*) [MC12 [MC23 full]]]]]]]]]. 
  subst.
  destruct (core_at_external12 _ _ _ _ _ _ _ _ _ _ _ MC12 AtExtSrc)
    as [MInj12 [MRR1 [MRR2 [vals2 [ArgsInj12 AtExt2]]]]]; 
     clear core_at_external12.
  destruct (core_at_external23 _ _ _ _ _ _ _ _ _ _ _ MC23 AtExt2)
    as [MInj23 [_ [MRR3 [vals3 [ArgsInj23 AtExtTgt]]]]]; 
     clear core_at_external23.
    split. eapply Mem.inject_compose; eassumption.
    split; trivial.
    split; trivial.
    exists vals3.
    split. eapply forall_val_inject_compose; try eassumption.
    assumption. }
{ (*after_external*)
  clear - match_wd12 match_valid12 core_at_external12 
          eff_after_external12  
          match_wd23 match_valid23 core_at_external23 
          eff_after_external23 senvs_equiv23 match_genv12 match_genv23
          (*ginfos_pres23 ginfos_pres12 *) senvs_equiv12.
  intros. rename st2 into st3. rename m2 into m3. rename L2 into L3. 
          rename vals2 into vals3'. rename m2' into m3'.
          rename RDO2 into RDO3. rename ret2 into ret3.
  destruct cd as [[d12 cc2] d23].
  destruct MatchMu as [st2 [m2 [j12 [j23 [L2 [Hst2 [HMu (*[GLUEINV*) [MC12 [MC23 full]]]]]]]]].
  assert (WDmu12:= match_wd12 _ _ _ _ _ _ _ _ MC12).
  assert (WDmu23:= match_wd23 _ _ _ _ _ _ _ _ MC23).
(*
  remember (fun b => match j b with None => None | Some _ => j12 b end) as jj12.
  assert (J: j = compose_meminj jj12 j23).
  { subst j jj12. extensionality b. unfold compose_meminj.
    destruct (j12 b); trivial. destruct p.
    remember (j23 b0) as d. destruct d; trivial. destruct p. rewrite <- Heqd. trivial. }
  clear HMu.*)
(*  remember (fun b => locBlocksSrc mu12 b || frgnBlocksSrc mu12 b || mapped (as_inj (compose_sm mu12 mu23)) b ) as RESTR.*)
(*  assert (NormMC12: match_core12 d12 j12 L1 st1 m1 L2 st2 m2) by assumption.
  remember mu12 as nmu12.
  assert (HmuNorm: mu = compose_sm nmu12 mu23).
     clear UnchLOOR13 UnchPrivSrc Mu'Hyp mu' frgnTgtHyp frgnTgt'
              frgnSrcHyp frgnSrc' FwdTgt FwdSrc RValInjNu' MemInjNu' 
              SMvalNu' WDnu' (*SEP*) INC ret2 ret1 (*nu'*) NuHyp (*nu*)
              (* GlobalsSeparate: SMvalNu' WDnu' INC ret2 m1' ret1 NuHyp*)
              pubTgtHyp pubTgt' pubSrcHyp pubSrc' ValInjMu AtExtTgt 
              AtExtSrc eff_after_external23 core_at_external23 
              eff_after_external12 core_at_external12 HasTy1 HasTy2. 
      subst nmu12 mu RESTR. unfold compose_sm; simpl.
          auto. 
  clear MC12. 
  assert (WDnmu12:= match_sm_wd12 _ _ _ _ _ _ NormMC12).
  clear HMu.*)
  assert (WDmu: forall (b1 b2 : block) (d0 : Z), j b1 = Some (b2, d0) -> L1 b1 = L3 b2).
  { subst j; intros. destruct (compose_meminjD_Some _ _ _ _ _ H) as [? [? [? [? [? ?]]]]]; subst d0; clear H.
    rewrite (WDmu12 _ _ _ H0). apply (WDmu23 _ _ _ H1). }
  assert (mu12_valid:= match_valid12 _ _ _ _ _ _ _ _ MC12).
  assert (mu23_valid:= match_valid23 _ _ _ _ _ _ _ _ MC23).
  destruct (core_at_external12 _ _ _ _ _ _ _ _ _ _ _ MC12 AtExtSrc)
   as [MInj12 [MRR1 [MRR2 [vals2 [ArgsInj12 (*[ArgsHT2*) AtExt2(*]*)]]]]]; clear core_at_external12.
  destruct (core_at_external23 _ _ _ _ _ _ _ _ _ _ _ MC23 AtExt2)
   as [MInj23 [_ [MRR3 [vals3 [ArgsInj23 (*[ArgsHT3*) AtExt3(*]*)]]]]]; clear core_at_external23.
  
  (** Prove uniqueness of e, ef_sig, vals3. We do this by hand, instead of 
     rewrite AtExtTgt in AtExt3; inv Atext3 in order to avoid the subst
     that's inherent in inv AtExt3. Probably there's a better way to do this... *)
  assert (e' = e /\ efsig'=efsig /\ vals3'=vals3).
     rewrite AtExtTgt in AtExt3. inv AtExt3. intuition.
  destruct H as [HH1 [HH2 HH3]].
  rewrite HH1, HH2, HH3 in *. clear HH1 HH2 HH3 e' efsig' vals3' AtExt3.

  specialize (eff_after_external12 _ _ _ _ _ _ _ _ _ _ _ _ _ _ MInj12 
        MC12 AtExtSrc AtExt2 ArgsInj12). 
  specialize (eff_after_external23 _ _ _ _ _ _ _ _ _ _ _ _ _ _ MInj23
        MC23 AtExt2 AtExtTgt ArgsInj23).

  assert (HeqB3: forall b3, ReadOnlyBlocks g3 b3 = true -> L3 b3 = false) by admit.
  assert (HeqB1B2: forall b1, ReadOnlyBlocks g1 b1 = true ->
         exists b2 d1, j12 b1 = Some (b2, d1) /\ ReadOnlyBlocks g2 b2 = true) by admit.
  assert (HeqB2B3: forall b2, ReadOnlyBlocks g2 b2 = true ->
         exists b3 d2, j23 b2 = Some (b3, d2) /\ ReadOnlyBlocks g3 b3 = true) by admit.
  exploit (interp_II m1 m2 j12 L1 L2 L3). eassumption. eassumption. eassumption. eassumption. eassumption. eassumption.
   eassumption. eassumption. eassumption. eassumption. eassumption. eassumption.
   eassumption. eassumption. eassumption. eassumption. eassumption. eassumption.
   eassumption. eassumption. eassumption. 

  intros [m2' [j12' [j23' [J' [Incr12 [Incr23 [InjValid12' [InjValid23' (*[Pure'*)
        [MInj12' [Fwd2 [MInj23' (* [nu12'valid
        [nu23'valid [GLUEINV'*) [full' [RDO_fwd2 [UnchMidA UnchMidB (*[Pure12 Pure23]*)]]]]]]]]]]]]]].

  assert (OOR: forall b ofs, o_o_reach j23 L3 m2 b ofs ->
           Mem.valid_block m3 b -> o_o_reach j L3 m1 b ofs).
  { clear - MInj12 HMu; intros. destruct H. split; intros; trivial.
    intros N. subst j.
    destruct (compose_meminjD_Some _ _ _ _ _ J) as [? [? [? [? [? ?]]]]].
    subst delta; clear J. 
    exploit Mem.perm_inject. apply H2. apply MInj12. eassumption.
    assert (Arith: ofs - (x0 + x1) + x0 = ofs - x1) by omega.
    rewrite Arith. eapply H1; eassumption. }   

  assert (Unch3: Mem.unchanged_on (o_o_reach j23 L3 m2) m3 m3').
  { destruct UnchTgt. constructor; trivial; intros.
    + eapply unchanged_on_perm; eauto.
    + specialize (Mem.perm_valid_block _ _ _ _ _ H0); intros.
      eapply unchanged_on_contents; eauto. } 

  (*next, prepare for application of eff_after_external12*)
  assert (H: exists ret2, val_inject j12' ret1 ret2 /\ 
                       val_inject j23' ret2 ret3 /\
                       Val.has_type ret2 (proj_sig_res efsig)). 
  { subst. 
    destruct (val_inject_split _ _ _ _ RValInjNu')
      as [ret2 [RValInjNu12' RValInjNu23']].  
    exists ret2. repeat (split; trivial).
    eapply valinject_hastype; eassumption. }
  destruct H as [ret2 [RValInjNu12' [RValInjNu23' RetType2]]].
  subst. 

  assert (UnchUnmappedSrc: Mem.unchanged_on (fun b1 z => L1 b1=true /\ j12 b1 = None) m1 m1').
  { clear - UnchSrc. destruct UnchSrc. constructor; trivial; intros.
    + apply unchanged_on_perm; trivial. destruct H as [Hb1 Hb2]. 
      unfold compose_meminj; rewrite Hb2. split; trivial.
    + apply unchanged_on_contents; trivial. destruct H as [Hb1 Hb2]. 
      unfold compose_meminj; rewrite Hb2. split; trivial. }
 
  exploit (eff_after_external12 j12' ret1 m1' ret2 m2'); trivial.
  { admit. (*globals_separate g2 j12 j12'*) }

  intros [d12' [c1' [c2' [AftExt1 [AftExt22 MC12']]]]]; clear eff_after_external12.

  exploit (eff_after_external23 j23' ret2 m2' ret3 m3'); trivial.
  { admit. (*globals_separate g3 j23 j23'*) }

  intros [d23' [c22' [c3' [AftExt2 [AftExt3 MC23']]]]]; clear eff_after_external23.

  rewrite AftExt2 in AftExt22; inv AftExt22.  
  exists (d12', Some c2', d23').
  exists c1'. exists c3'.
  split. assumption.
  split. assumption.
  exists c2', m2', j12', j23', L2.
  split. trivial.
  split. trivial.
  split. assumption.
  split; assumption. 
Admitted. (*remaining admits are about readonly or global blocks*)  

End Eff_sim_trans. 