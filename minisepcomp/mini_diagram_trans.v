Require Import compcert.common.Events.
Require Import compcert.common.Memory.
Require Import compcert.lib.Coqlib.
Require Import compcert.common.Values.
Require Import compcert.lib.Maps.
Require Import compcert.lib.Integers.
Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.
Require Import msl.Axioms.

Require Import sepcomp.mem_lemmas. (*needed for definition of mem_forward etc*)
Require Import sepcomp.semantics.
Require Import sepcomp.semantics_lemmas.
Require Import sepcomp.effect_semantics.

Require Import Wellfounded.
Require Import Relations.

Require Import minisepcomp.mini_simulations.
Require Import minisepcomp.mini_simulations_lemmas.
(*
Definition entrypoints_compose 
  (ep12 ep23 ep13 : list (val * val * signature)): Prop :=
  forall v1 v3 sig, In (v1,v3,sig) ep13 =
    exists v2, In (v1,v2,sig) ep12 /\ In (v2,v3,sig) ep23.
*)
Section CoreDiagrams_trans.

Context {F1 V1 C1 F2 V2 C2 F3 V3 C3:Type}
        (Sem1 : @EffectSem (Genv.t F1 V1) C1)
        (Sem2 : @EffectSem (Genv.t F2 V2) C2)
        (Sem3 : @EffectSem (Genv.t F3 V3) C3)
        (g1 : Genv.t F1 V1)
        (g2 : Genv.t F2 V2)
        (g3 : Genv.t F3 V3).

Lemma ext_inj_diagram: forall 
(GNE12: genv_next_eq g1 g2)
(core_data12 : Type)
(match_core12 : core_data12 -> C1 -> mem -> (block -> bool) -> C2 -> mem -> Prop)
(core_ord12 : core_data12 -> core_data12 -> Prop)
(match_localblocks12: forall d c1 m1 L c2 m2,  match_core12 d c1 m1 L c2 m2 -> 
      forall b, L b = true -> (Mem.valid_block m1 b /\ Mem.valid_block m2 b))
(effcore_diagram12 : forall (st1 : C1) (m1 : mem) (st1' : C1) (m1' : mem)
                      (U1 : block -> Z -> bool),
                    effstep Sem1 g1 U1 st1 m1 st1' m1' ->
                    forall (cd : core_data12) (st2 : C2) (m2 : mem) (L : block -> bool),
                    match_core12 cd st1 m1 L st2 m2 ->
                    exists
                      (st2' : C2) (m2' : mem) (cd' : core_data12) 
                    (L' : block -> bool),
                      L' = (fun b : block => L b || freshblock m1 m1' b) /\
                      L' = (fun b : block => L b || freshblock m2 m2' b) /\
                      match_core12 cd' st1' m1' L' st2' m2' /\
                      (exists U2 : block -> Z -> bool,
                         (effstep_plus Sem2 g2 U2 st2 m2 st2' m2' \/
                          effstep_star Sem2 g2 U2 st2 m2 st2' m2' /\ core_ord12 cd' cd) /\
                         (forall (b : block) (ofs : Z),
                          U2 b ofs = true -> L b = true \/ U1 b ofs = true)))
(core_data23 : Type)
(match_core23 : core_data23 ->
               meminj ->
               (block -> bool) -> C2 -> mem -> (block -> bool) -> C3 -> mem -> Prop)
(core_ord23 : core_data23 -> core_data23 -> Prop)
(match_wd23 : forall (d : core_data23) (j : meminj) (L1 : block -> bool) 
               (c1 : C2) (m1 : mem) (L2 : block -> bool) (c2 : C3) 
               (m2 : mem),
             match_core23 d j L1 c1 m1 L2 c2 m2 ->
             forall (b1 b2 : block) (d0 : Z), j b1 = Some (b2, d0) -> L1 b1 = L2 b2)
(match_valid23 : forall (d : core_data23) (j : meminj) (L1 : block -> bool) 
                  (c1 : C2) (m1 : mem) (L2 : block -> bool) (c2 : C3) 
                  (m2 : mem),
                match_core23 d j L1 c1 m1 L2 c2 m2 -> meminj_valid j L1 m1 L2 m2)
(effcore_diagram23 : forall (st1 : C2) (m1 : mem) (st1' : C2) (m1' : mem)
                      (U1 : block -> Z -> bool),
                    effstep Sem2 g2 U1 st1 m1 st1' m1' ->
                    forall (cd : core_data23) (st2 : C3) (j : meminj) 
                      (m2 : mem) (L1 L2 : block -> bool),
                    match_core23 cd j L1 st1 m1 L2 st2 m2 ->
                    exists
                      (st2' : C3) (m2' : mem) (cd' : core_data23) 
                    (j' : meminj) (L1' L2' : block -> bool),
                      mini_intern_incr j j' L1' L2' /\
                      globals_separate m1 g3 j j' /\
                      mini_locally_allocated L1 L2 m1 m2 L1' L2' m1' m2' /\
                      match_core23 cd' j' L1' st1' m1' L2' st2' m2' /\
                      (exists U2 : block -> Z -> bool,
                         (effstep_plus Sem3 g3 U2 st2 m2 st2' m2' \/
                          effstep_star Sem3 g3 U2 st2 m2 st2' m2' /\ core_ord23 cd' cd) /\
                         ((forall (b1 : block) (z : Z),
                           U1 b1 z = true -> L1 b1 = true \/ j b1 <> None) ->
                          forall (b2 : block) (ofs : Z),
                          U2 b2 ofs = true ->
                          L2 b2 = true \/
                          (exists (b1 : block) (delta : Z),
                             j b1 = Some (b2, delta) /\ U1 b1 (ofs - delta) = true))))
st1 m1 st1' m1' U1 (CS1 : effstep Sem1 g1 U1 st1 m1 st1' m1')
d12 d23 st3 j m3 L1 L3 st2 m2
(MC12 : match_core12 d12 st1 m1 L1 st2 m2)
(MC23 : match_core23 d23 j L1 st2 m2 L3 st3 m3),
exists
  (st3' : C3) (m3' : mem) (cd' : core_data12 * option C2 * core_data23) 
(j' : meminj) (L1' L3' : block -> bool),
  mini_intern_incr j j' L1' L3' /\
  globals_separate m1 g3 j j' /\
  mini_locally_allocated L1 L3 m1 m3 L1' L3' m1' m3' /\
  (let (y, d2) := cd' in
   let (d1, X) := y in
   exists (c2 : C2) (m2' : mem),
     X = Some c2 /\
     match_core12 d1 st1' m1' L1' c2 m2' /\ match_core23 d2 j' L1' c2 m2' L3' st3' m3') /\
  (exists U3 : block -> Z -> bool,
     (effstep_plus Sem3 g3 U3 st3 m3 st3' m3' \/
      effstep_star Sem3 g3 U3 st3 m3 st3' m3' /\
      clos_trans (core_data12 * option C2 * core_data23)
        (sem_compose_ord_eq_eq core_ord12 core_ord23 C2) cd' (d12, Some st2, d23)) /\
     ((forall (b1 : block) (z : Z), U1 b1 z = true -> L1 b1 = true \/ j b1 <> None) ->
      forall (b2 : block) (ofs : Z),
      U3 b2 ofs = true ->
      L3 b2 = true \/
      (exists (b1 : block) (delta : Z),
         j b1 = Some (b2, delta) /\ U1 b1 (ofs - delta) = true))).
Proof. intros.
  destruct (effcore_diagram12 _ _ _ _ _ CS1 _ _ _ _ MC12)
    as [st2' [m2' [d12' [L1' [HL1' [HL2' [MC12' [U2 [Y MOD12]]]]]]]]]; clear effcore_diagram12.
  assert (ZZ: effstep_plus Sem2 g2 U2 st2 m2 st2' m2' \/
    (st2,m2) = (st2',m2') /\ core_ord12 d12' d12).
  destruct Y. auto.
  destruct H.
  destruct H. destruct x.
  right. simpl in H. destruct H. split; auto.
  left. exists x; auto.
  clear Y. destruct ZZ as [CS2 | [CS2 ord12']].
 (*case1*) 
+ destruct CS2.
  clear CS1. 
  cut (exists st3' : C3,  exists m3' : mem, 
    exists d23':core_data23, exists j', exists L22', exists L3',
      mini_intern_incr j j' L22' L3' /\
      globals_separate m2 g3 j j' /\
    mini_locally_allocated L1 L3 m2 m3 L22' L3' m2' m3' /\
    match_core23 d23' j' L22' st2' m2' L3' st3' m3' /\
    (exists U3,
      (effstep_plus Sem3 g3 U3 st3 m3 st3' m3' \/
        (effstep_star Sem3 g3 U3 st3 m3 st3' m3' /\
        clos_trans (core_data12 * option C2 * core_data23)
        (sem_compose_ord_eq_eq core_ord12 core_ord23 C2) 
               (d12', Some st2', d23')
        (d12, Some st2,d23)))
    /\ ((forall b2 z, U2 b2 z = true -> L1 b2 = true \/ j b2 <> None) ->
      forall (b3 : block) (ofs : Z),
      U3 b3 ofs = true ->
      L3 b3 = true \/
      (exists (b2 : block) (delta : Z),
         j b2 = Some (b3, delta) /\ U2 b2 (ofs - delta) = true)))).
  - intros [st3' [m3' [d23' [j' [L22' [L3' (*[INV'*) [InjIncr23 
          [Gsep23 [LocAlloc23 [MC23' [U3 [ZZ MOD23]]]]]]]]]]]].
    exists st3'. exists m3'. 
    exists (d12', Some st2', d23').
    exists j', L1', L3'.
    assert (L22' = L1').
    { clear - HL2' LocAlloc23. destruct LocAlloc23. subst. reflexivity. }
    subst L22'.
    split. assumption.
    split. { clear ZZ MOD23. red; intros. destruct (Gsep23 _ _ _ J J'); clear Gsep23. split; trivial.
             intros N. elim H0; clear H0. destruct InjIncr23 as [INC SEP].
             destruct (SEP _ _ _ J J').
             assert ((fun b : block => L1 b || freshblock m1 m1' b) b1 = true). rewrite HL1' in H0; trivial. clear HL1'; simpl in H3; subst L1'.
             case_eq (L1 b1); intros ZZ; rewrite ZZ in *; simpl in  *. apply (match_localblocks12 _ _ _ _ _ _ MC12 _ ZZ).
             apply freshblockProp_char in H3. destruct H3; congruence. }
    split. { split. assumption. destruct LocAlloc23. assumption. }  
    split.
    { exists st2', m2'. clear ZZ. intuition. }  
    exists U3. split. apply ZZ. 
    intros. 
    assert (M12H: forall (b2 : block) (z : Z), U2 b2 z = true -> L1 b2 = true \/ j b2 <> None).
    { intros. destruct (MOD12 _ _ H2); [ left; trivial |  apply (H0 _ _ H3)]. }
    destruct (MOD23 M12H _ _ H1); clear M12H MOD23.
    * left; trivial.
    * destruct H2 as [b1 [d [? ?]]].
      destruct (MOD12 _ _ H3).
      solve [ left; rewrite <- (match_wd23 _ _ _ _ _ _ _ _ MC23 _ _ _ H2); trivial].
      right; exists b1, d; split; trivial.
  -  
  clear MC12 MC12' HL1' MOD12. 
  clear st1 m1 st1' m1' GNE12. 
  clear match_localblocks12 C1 Sem1 match_core12 g1 U1. clear HL2' HL2' L1'.
  revert U2 j d23 st2 m2 st3 m3 H L1 L3 MC23. 
  induction x; intros. 
  {
   (*base case*) simpl in H.
    destruct H as [c2 [m2'' [U3 [U4 [? [? ?]]]]]].
    destruct H0. inv H0; simpl in *. 
    destruct (effcore_diagram23 _ _ _ _ _ H _ _ _ _ _ _ MC23) 
      as [st3' [m3' [d23' [j23' [L22' [L3' [InjIncr23 
          [Gsep23 [LocAlloc23 [MC23' [U5 [? MOD32]]]]]]]]]]]]; clear effcore_diagram23.
    exists st3'. exists m3'. exists d23'. exists j23', L22', L3'. 
    split. trivial. 
    split. trivial. 
    split. trivial. 
    split. trivial. 
    exists U5. 
    split. destruct H0. left; assumption.
           destruct H0. right. split; trivial.
           apply t_step. constructor 2. apply H1.
    intros.  
      assert (U3Hyp': forall b1 z, U3 b1 z = true -> L1 b1 = true \/ j b1 <> None).
      { intros. eapply (H1 b1 z). rewrite H3; trivial. }
      clear H1.
      destruct (MOD32 U3Hyp' _ _ H2). left; trivial. 
      destruct H1 as [? [? [? ?]]].
      right. exists x, x0. rewrite H3. split; trivial. }
  {
   (*inductive case*)
    remember (S x) as x'. simpl in H.
    rename st2' into st2''. rename m2' into m2''.
    destruct H as [st2' [m2' [U4 [U3 [Step2 [StepN2 HU]]]]]]. subst x'.
    destruct (effcore_diagram23 _ _ _ _ _ Step2 _ _ _ _ _ _ MC23) 
      as [c3' [m3' [d23' [j23' [L2a' [L3a' [InjInc23  
             [Gsep23 [LocAlloc23 [MC23' [U5 [Steps3 MOD23]]]]]]]]]]]]; clear effcore_diagram23.
    assert (FWD2: mem_forward m2 m2').
        eapply effstep_fwd; eassumption.
    assert (FWD2': mem_forward m2' m2'').
        eapply effstepN_fwd; eassumption.
    assert (FWD3: mem_forward m3 m3').
        destruct Steps3 as [[n K] | [[n K] _]];
             eapply effstepN_fwd; eassumption.
    destruct (IHx _ j23' d23' _ _ c3' m3' StepN2 _ _ MC23') 
        as [c3'' [m3'' [d23'' [j23'' [LL2 [LL3 [InjIncr' 
             [Gsep' [LocAlloc23' [MC23'' [U3' [StepN3 MOD23']]]]]]]]]]]]; clear IHx.
    assert (FWD3': mem_forward m3' m3'').
        destruct StepN3 as [[n K] | [[n K] _]];
             eapply effstepN_fwd; eassumption.
    exists c3''. exists m3''. exists d23''. exists j23'', LL2, LL3.
    split. { (*mini_intern_trans*) clear - InjIncr' InjInc23 LocAlloc23'.
             destruct InjIncr'; destruct InjInc23. destruct LocAlloc23'; subst.
             split. eapply inject_incr_trans; eassumption.
             intros. remember(j23' b1) as q.
             destruct q; symmetry in Heqq.
             + destruct p. specialize (H _ _ _ Heqq). rewrite J' in H. inv H.
               destruct (H2 _ _ _ J Heqq). rewrite H, H3; simpl. split; trivial.
             + apply (H0 _ _ _ Heqq J'). } 
    split. { clear - InjIncr' InjInc23 Gsep' Gsep23 FWD2.
             destruct InjIncr'; destruct InjInc23. 
             red; intros. remember(j23' b1) as q.
             destruct q; symmetry in Heqq.
             + destruct p. specialize (H _ _ _ Heqq). rewrite J' in H. inv H.
               apply (Gsep23 _ _ _ J Heqq). 
             + destruct (Gsep' _ _ _ Heqq J'). split; trivial.
               intros N. elim H3; clear H3. apply FWD2; eauto. }
    split. { specialize (freshblock_trans _ _ _ FWD2 FWD2'); intros FW2.
             specialize (freshblock_trans _ _ _ FWD3 FWD3'); intros FW3.
             clear - FW2 FW3 LocAlloc23 LocAlloc23'.
             destruct LocAlloc23; subst. destruct LocAlloc23'; subst.
             split; extensionality b. 
             + rewrite <- orb_assoc, FW2; trivial.
             + rewrite <- orb_assoc, FW3; trivial. }
    split. apply MC23''.
    exists (fun b z => U5 b z || (U3' b z && valid_block_dec m3 b)). 
    split. clear MOD23 MOD23'. 
           destruct Steps3; destruct StepN3.
           (*1/4*)
              left. eapply effstep_plus_trans; eassumption.
           (*2/4*)
              left. destruct H0 as [EFF3 CT].
              eapply effstep_plus_star_trans; eassumption. 
           (*3/4*)
               left. destruct H as [EFF3 CORD].
               eapply effstep_star_plus_trans; eassumption.
           (*4/4*)
               right. destruct H as [EFF3 CORD].
                      destruct H0 as [EFF3' CT].
               split. eapply effstep_star_trans; eassumption.
               eapply t_trans.
                 apply CT. clear CT.  
                 apply t_step.
                 constructor 2. apply CORD.
    (*MOD23-clause*) subst U2. intros U4Hyp b3 ofs HU3.
      apply orb_true_iff in HU3.
      destruct HU3.
      - assert (U4Hyp': forall b1 z, U4 b1 z = true -> L1 b1 = true \/ j b1 <> None).
        { intros. apply (U4Hyp b1 z). rewrite H0; trivial. }
        destruct (MOD23 U4Hyp' _ _ H). left; trivial.
        right. destruct H0 as [? [? [? ?]]]. exists x0, x1; rewrite H1; split; trivial.
      - apply andb_true_iff in H. destruct H.
         destruct (valid_block_dec m3 b3); try inv H0.
         assert (U3Hyp: forall b z, U3 b z = true -> L2a' b = true \/ j23' b <> None).
         { intros. 
           assert (U3valid:= effstepN_valid _ _ _ _ _ _ _ _ StepN2 _ _ H0).
           specialize (U4Hyp b z). rewrite H0 in U4Hyp; simpl in U4Hyp.
           destruct (valid_block_dec m2 b); simpl in U4Hyp.
           * rewrite orb_true_r in U4Hyp.
             destruct LocAlloc23; subst. 
             destruct U4Hyp; trivial.
             left. rewrite H1; trivial.
             right. remember (j b) as q. destruct q; try solve [congruence].
                    symmetry in Heqq; destruct p. destruct InjInc23 as [II _].
                    rewrite (II _ _ _ Heqq). discriminate.
           * rewrite orb_false_r in U4Hyp.
             destruct LocAlloc23. subst. left.
             assert (freshblockProp m2 m2' b) by (split; trivial).
             rewrite freshblock_asProp in H1. unfold asProp in H1; rewrite H1; apply orb_true_r. 
         }
         destruct (MOD23' U3Hyp _ _ H); clear MOD23'.
         * destruct LocAlloc23; subst.
           apply orb_true_iff in H0. destruct H0. left; trivial.
           apply freshblockProp_char in H0.
           destruct H0. contradiction.
         * destruct H0 as [? [? [? ?]]].
           destruct InjInc23 as [II23a II23b].
           remember (j x0) as q.
           destruct q; symmetry in Heqq.
           + destruct p; specialize (II23a _ _ _ Heqq). rewrite II23a in H0. inv H0.
             right. exists x0, x1. split; trivial. rewrite H1. simpl.
             destruct (match_valid23 _ _ _ _ _ _ _ _ MC23) as [A [ B C]].
             destruct (C _ _ _ Heqq). destruct (valid_block_dec m2 x0); try contradiction. apply orb_true_r.
           + destruct (II23b _ _ _ Heqq H0). destruct LocAlloc23; subst.
             apply orb_true_iff in H3. destruct H3. left; trivial.
             apply freshblockProp_char in H3.
             destruct H3; contradiction.
  }
+
  (*case 2*)
   inversion CS2; clear CS2. subst st2 m2.
   assert (L1' = L1).
   { rewrite HL2'. extensionality b. rewrite freshblock_irrefl; apply orb_false_r. } 
   clear HL2'. rewrite H in *. clear H L1'.  
   exists st3. exists m3.
   exists (d12',Some st2',d23), j, L1, L3.
   split. { split; intros. apply inject_incr_refl. congruence. }
   split. { red; intros; congruence. }
   split. { split; trivial.
            extensionality b. rewrite freshblock_irrefl, orb_false_r; trivial. }
   split.
   { clear effcore_diagram23.
     exists st2'. exists m2'. repeat split; auto. }

   exists (fun b z => false). 
    split. right. split. exists O. simpl; auto.
    apply t_step. constructor 1; auto. intros; discriminate.
Qed.

Lemma effcore_diagram_trans: forall
(core_data12 : Type)
(match_core12 : core_data12 -> meminj ->
               (block -> bool) -> C1 -> mem -> (block -> bool) -> C2 -> mem -> Prop)
(core_ord12 : core_data12 -> core_data12 -> Prop)
(match_valid12 : forall (d : core_data12) (j : meminj) (L1 : block -> bool) 
                  (c1 : C1) (m1 : mem) (L2 : block -> bool) 
                  (c2 : C2) (m2 : mem),
                match_core12 d j L1 c1 m1 L2 c2 m2 -> meminj_valid j L1 m1 L2 m2)
(match_wd12:  forall d j L1 c1 m1 L2 c2 m2 (MS: match_core12 d j L1 c1 m1 L2 c2 m2)
               b1 b2 d (J:j b1=Some(b2, d)), L1 b1 = L2 b2)
(effcore_diagram12 : forall (st1 : C1) (m1 : mem) (st1' : C1) 
                      (m1' : mem) (U1 : block -> Z -> bool),
                    effstep Sem1 g1 U1 st1 m1 st1' m1' ->
                    forall (cd : core_data12) (st2 : C2) (j : meminj) 
                      (m2 : mem) (L1 L2 : block -> bool),
                    match_core12 cd j L1 st1 m1 L2 st2 m2 ->
                    exists
                      (st2' : C2) (m2' : mem) (cd' : core_data12) 
                    (j' : meminj) (L1' L2' : block -> bool),
                      mini_intern_incr j j' L1' L2' /\
                      globals_separate m1 g2 j j' /\
                      mini_locally_allocated L1 L2 m1 m2 L1' L2' m1' m2' /\
                      match_core12 cd' j' L1' st1' m1' L2' st2' m2' /\
                      (exists U2 : block -> Z -> bool,
                         (effstep_plus Sem2 g2 U2 st2 m2 st2' m2' \/
                          effstep_star Sem2 g2 U2 st2 m2 st2' m2' /\ core_ord12 cd' cd) /\
                         ((forall (b1 : block) (z : Z),
                           U1 b1 z = true -> L1 b1 = true \/ j b1 <> None) ->
                          forall (b2 : block) (ofs : Z),
                          U2 b2 ofs = true ->
                          L2 b2 = true \/
                          (exists (b1 : block) (delta : Z),
                             j b1 = Some (b2, delta) /\ U1 b1 (ofs - delta) = true))))
(core_data23 : Type)
(match_core23 : core_data23 -> meminj ->
               (block -> bool) -> C2 -> mem -> (block -> bool) -> C3 -> mem -> Prop)
(core_ord23 : core_data23 -> core_data23 -> Prop)
(*(genvs_dom_eq23 : genvs_domain_eq g2 g3)*)
(match_genv23 : forall (d : core_data23) (j : meminj) (L1 : block -> bool) 
                 (c1 : C2) (m1 : mem) (L2 : block -> bool) 
                 (c2 : C3) (m2 : mem),
               match_core23 d j L1 c1 m1 L2 c2 m2 ->
               meminj_preserves_globals g2 j /\
               (forall b : block, isGlobalBlock g2 b = true -> j b <> None))
(match_valid23 : forall (d : core_data23) (j : meminj) (L1 : block -> bool) 
                  (c1 : C2) (m1 : mem) (L2 : block -> bool) 
                  (c2 : C3) (m2 : mem),
                match_core23 d j L1 c1 m1 L2 c2 m2 -> meminj_valid j L1 m1 L2 m2)
(match_wd23:  
    forall d j L1 c1 m1 L2 c2 m2 (MS: match_core23 d j L1 c1 m1 L2 c2 m2)
    b1 b2 d (J:j b1=Some(b2, d)), L1 b1 = L2 b2 )
(effcore_diagram23 : forall (st1 : C2) (m1 : mem) (st1' : C2) 
                      (m1' : mem) (U1 : block -> Z -> bool),
                    effstep Sem2 g2 U1 st1 m1 st1' m1' ->
                    forall (cd : core_data23) (st2 : C3) (j : meminj) 
                      (m2 : mem) (L1 L2 : block -> bool),
                    match_core23 cd j L1 st1 m1 L2 st2 m2 ->
                    exists
                      (st2' : C3) (m2' : mem) (cd' : core_data23) 
                    (j' : meminj) (L1' L2' : block -> bool),
                      mini_intern_incr j j' L1' L2' /\
                      globals_separate m1 g3 j j' /\
                      mini_locally_allocated L1 L2 m1 m2 L1' L2' m1' m2' /\
                      match_core23 cd' j' L1' st1' m1' L2' st2' m2' /\
                      (exists U2 : block -> Z -> bool,
                         (effstep_plus Sem3 g3 U2 st2 m2 st2' m2' \/
                          effstep_star Sem3 g3 U2 st2 m2 st2' m2' /\ core_ord23 cd' cd) /\
                         ((forall (b1 : block) (z : Z),
                           U1 b1 z = true -> L1 b1 = true \/ j b1 <> None) ->
                          forall (b2 : block) (ofs : Z),
                          U2 b2 ofs = true ->
                          L2 b2 = true \/
                          (exists (b1 : block) (delta : Z),
                             j b1 = Some (b2, delta) /\ U1 b1 (ofs - delta) = true))))
st1 m1 st1' m1' U1 (CS1: effstep Sem1 g1 U1 st1 m1 st1' m1') d12 d23 st3 m3 L1 L3
st2 m2 j12 j23 L2 (MC12 : match_core12 d12 j12 L1 st1 m1 L2 st2 m2)
(MC23 : match_core23 d23 j23 L2 st2 m2 L3 st3 m3)
(full : full_ext j12 j23 L1 L2),
exists
  (st3' : C3) (m3' : mem) (cd' : core_data12 * option C2 * core_data23) 
(j' : meminj) (L1' L3' : block -> bool),
  mini_intern_incr (compose_meminj j12 j23) j' L1' L3' /\
  globals_separate m1 g3 (compose_meminj j12 j23) j' /\
  mini_locally_allocated L1 L3 m1 m3 L1' L3' m1' m3' /\
  (let (y, d2) := cd' in
   let (d1, X) := y in
   exists (c2' : C2) (m2' : mem) (j1' j2' : meminj) (L2' : block -> bool),
     X = Some c2' /\
     j' = compose_meminj j1' j2' /\
     match_core12 d1 j1' L1' st1' m1' L2' c2' m2' /\
     match_core23 d2 j2' L2' c2' m2' L3' st3' m3' /\ full_ext j1' j2' L1' L2') /\
  (exists U2 : block -> Z -> bool,
     (effstep_plus Sem3 g3 U2 st3 m3 st3' m3' \/
      effstep_star Sem3 g3 U2 st3 m3 st3' m3' /\
      clos_trans (core_data12 * option C2 * core_data23)
        (sem_compose_ord_eq_eq core_ord12 core_ord23 C2) cd' 
        (d12, Some st2, d23)) /\
     ((forall (b1 : block) (z : Z),
       U1 b1 z = true -> L1 b1 = true \/ compose_meminj j12 j23 b1 <> None) ->
      forall (b2 : block) (ofs : Z),
      U2 b2 ofs = true ->
      L3 b2 = true \/
      (exists (b1 : block) (delta : Z),
         compose_meminj j12 j23 b1 = Some (b2, delta) /\ U1 b1 (ofs - delta) = true))).
Proof. intros. 
  destruct (effcore_diagram12 _ _ _ _ _ CS1 _ _ _ _ _ _ MC12)
    as [st2' [m2' [d12' [j12' [L1' [L2' [InjIncr12 [Gsep [LocAlloc12
       [MC12' [U2 [Y MOD12]]]]]]]]]]]]; clear effcore_diagram12.
  assert (ZZ: effstep_plus Sem2 g2 U2 st2 m2 st2' m2' \/
    (st2,m2) = (st2',m2') /\ core_ord12 d12' d12).
  destruct Y. auto.
  destruct H.
  destruct H. destruct x.
  right. simpl in H. destruct H. split; auto.
  left. exists x; auto.
  clear Y. destruct ZZ as [CS2 | [CS2 ord12']].
 (*case1*) 
+ destruct CS2.
  clear CS1. rename Gsep into Gsep12.
  cut (exists st3' : C3,  exists m3' : mem, 
    exists d23':core_data23, exists j23', exists L22', exists L3',
(*      (locBlocksTgt mu12' = locBlocksSrc mu23' /\
        extBlocksTgt mu12' = extBlocksSrc mu23' /\
      (forall b, pubBlocksTgt mu12' b = true -> pubBlocksSrc mu23' b = true) /\
      (forall b, frgnBlocksTgt mu12' b = true -> frgnBlocksSrc mu23' b = true)) /\ *)
      mini_intern_incr j23 j23' L22' L3' /\
      globals_separate m2 g3 j23 j23' /\
    (*sm_inject_separated mu23 mu23' m2 m3 /\ *)
    mini_locally_allocated L2 L3 m2 m3 L22' L3' m2' m3' /\
    match_core23 d23' j23' L22' st2' m2' L3' st3' m3' /\
    (exists U3,
      (effstep_plus Sem3 g3 U3 st3 m3 st3' m3' \/
        (effstep_star Sem3 g3 U3 st3 m3 st3' m3' /\
        clos_trans (core_data12 * option C2 * core_data23)
        (sem_compose_ord_eq_eq core_ord12 core_ord23 C2) 
               (d12', Some st2', d23')
        (d12, Some st2,d23)))
    /\ ((forall b2 z, U2 b2 z = true -> L2 b2 = true \/ j23 b2 <> None) ->
      forall (b3 : block) (ofs : Z),
      U3 b3 ofs = true ->
      L3 b3 = true \/
      (exists (b2 : block) (delta : Z),
         j23 b2 = Some (b3, delta) /\ U2 b2 (ofs - delta) = true)))).
  - intros [st3' [m3' [d23' [j23' [L22' [L3' (*[INV'*) [InjIncr23 
          [Gsep23 [LocAlloc23 [MC23' [U3 [ZZ MOD23]]]]]]]]]]]].
    exists st3'. exists m3'. 
    exists (d12', Some st2', d23').
    exists (compose_meminj j12' j23'), L1', L3'.
    assert (L22' = L2').
    { destruct LocAlloc12; subst. destruct LocAlloc23; subst. reflexivity. }
    subst L22'. split.
    { destruct InjIncr12 as [II12a II12b]; destruct InjIncr23 as [II23a II23b].
      split. eapply compose_meminj_inject_incr; eassumption. 
      intros b1 b3 d J J'. destruct (compose_meminjD_Some _ _ _ _ _ J') as [b2 [d1 [d2 [J12' [J23' D]]]]]; subst d; clear J'.
      exploit match_wd23. apply MC23'. eassumption. intros HL23'. rewrite <- HL23' in *.
      destruct (compose_meminjD_None _ _ _ J).
      + destruct (II12b _ _ _ H0 J12'). auto.
      + destruct H0 as [b2' [d1' [K12 K23']]].
        exploit match_wd12. apply MC12'. eassumption. intros HL12'. rewrite HL12' in *.
        specialize (II12a _ _ _ K12). rewrite J12' in II12a; inv II12a.
        specialize (II23b _ _ _ K23' J23'). inv J12'. destruct II23b.
        split; trivial. 
    }
    split.
    { intros b1 b3 d; intros.
       destruct (compose_meminjD_Some _ _ _ _ _ J') as [b2 [d1 [d2 [map12' [map23' extra]]]]]. subst d; clear J'.
       destruct (compose_meminjD_None _ _ _ J) as [map12| [b2' [d [map12 map23]]]].
       * destruct (Gsep12 _ _ _ map12 map12'). split; trivial.
         admit. (*assert (isGlobalBlock g2 b2 = false) by (eapply Gsep; eauto)
         destruct (isGlobalBlock g2 b3) eqn:isglob; [ | ].
         * apply (meminj_preserves_globals_isGlobalBlock _ _ pglobals) in isglob.
    apply WD23' in isglob. destruct isglob as [extS extT].
    rewrite <- (as_inj_extBlocks _ _ _ _ WD23' map23) in extT.
    rewrite <- (intern_incr_extBlocksSrc _ _ InjIncr23) in extT.
    destruct GLUE as [GLUEloc GLUEext].
    rewrite <- GLUEext in extT.
    apply as_injD_None in map12'. destruct map12' as [extmap12 locmap12].
    rewrite (intern_incr_extern _ _ InjIncr12) in extmap12.
    rewrite (intern_incr_extBlocksTgt _ _ InjIncr12) in extT.
    unfold as_inj, join in map12. rewrite extmap12 in map12.
    apply WD12' in map12.
    destruct map12 as [locS locT].
    destruct WD12' as [disj_src disj_tgt _].
    destruct (disj_tgt b2) as [theFalse | theFalse];
    rewrite theFalse in * ; discriminate.*)
       * assert (HH: j12' b1 = Some (b2', d))
         by (eapply InjIncr12; auto).
         rewrite HH in map12'; inversion map12'; subst.
         (*eapply Gsep23; eauto. *) destruct (Gsep23 _ _ _ map23 map23'). split; trivial.
         intros N. apply H0; clear H0.
         exploit match_valid12; try eapply MC12. intros [Z1 [Z2 Z3]]. apply (Z3 _ _ _ map12). 
    }
    split.
    { destruct LocAlloc12. destruct LocAlloc23. split; assumption. }
    split.
    { exists st2', m2', j12', j23', L2'. clear ZZ. intuition.
      red; intros. clear MOD23 H MOD12.
      exploit match_wd12. apply MC12'. eassumption. intros HL12'. rewrite <- HL12' in *. 
      split; trivial. red in full. red in Gsep12.
      destruct InjIncr12 as [II12a II12b].
      destruct InjIncr23 as [II23a II23b].
      remember (j12 b1) as j.
      destruct j; symmetry in Heqj.
      + destruct p. rewrite (II12a _ _ _ Heqj) in H1; inv H1.
        destruct (full b1 b2 delta1) as [HL2' [b3 [d2 J23]]]; trivial. 
        - remember (L1 b1) as l. destruct l; trivial. symmetry in Heql.
          clear - H0 Heql LocAlloc12. destruct LocAlloc12; subst. rewrite Heql in *; trivial.  
        - rewrite (II23a _ _ _ J23). eexists; eexists; reflexivity.
      + destruct (II12b _ _ _ Heqj H1). congruence.
    } 
    exists U3. split. apply ZZ.
    intros.
    assert (M12H: forall b1 z, U1 b1 z = true -> L1 b1 = true \/ j12 b1 <> None).
    { intros. destruct (H0 _ _ H2). left; trivial.
      right. intros N. elim H3; clear H3. unfold compose_meminj; rewrite N; trivial.
    }
    specialize (MOD12 M12H).
    assert (M23H: forall b2 z, U2 b2 z = true -> L2 b2 = true \/ j23 b2 <> None).
    { intros. clear MOD23. destruct (MOD12 _ _ H2). left; trivial.
      destruct H3 as [? [? [? ?]]]. 
       destruct (H0 _ _ H4).
       * left. destruct (match_wd12 _ _ _ _ _ _ _ _  MC12 _ _ _ H3); trivial.
       * right. intros N. elim H5; clear H5. unfold compose_meminj; rewrite H3, N; trivial.
    }
    specialize (MOD23 M23H). clear M12H M23H.
    destruct (MOD23 _ _ H1); clear MOD23. left; trivial.
    destruct H2 as [? [? [? ?]]].
    destruct (MOD12 _ _ H3); clear MOD12.
    * left. destruct (match_wd23 _ _ _ _ _ _ _ _  MC23 _ _ _ H2); trivial.
    * right. destruct H4 as [? [? [? ?]]].
      exists x2, (x3+x1). unfold compose_meminj; rewrite H4, H2. split; trivial.
      assert (Arith: ofs - (x3 + x1) = ofs - x1 - x3) by omega.
      rewrite Arith; trivial.
  -  
  clear MC12 InjIncr12 Gsep12 MC12' (*MatchHyp12*) full LocAlloc12 MOD12 match_valid12 match_wd12. 
  clear st1 m1 st1' m1' j12 j12'. 
  clear C1 Sem1 match_core12 g1.
  revert U2 j23 d23 st2 m2 st3 m3 H L2 L3 MC23. 
  induction x; intros. 
  {
   (*base case*) simpl in H.
    destruct H as [c2 [m2'' [U3 [U4 [? [? ?]]]]]].
    destruct H0. inv H0; simpl in *. 
    destruct (effcore_diagram23 _ _ _ _ _ H _ _ _ _ _ _ MC23) 
      as [st3' [m3' [d23' [j23' [L22' [L3' [InjIncr23 
          [Gsep23 [LocAlloc23 [MC23' [U5 [? MOD32]]]]]]]]]]]]; clear effcore_diagram23.
    exists st3'. exists m3'. exists d23'. exists j23', L22', L3'. 
    split. trivial. 
    split. trivial. 
    split. trivial. 
    split. trivial. 
    exists U5. 
    split. destruct H0. left; assumption.
           destruct H0. right. split; trivial.
           apply t_step. constructor 2. apply H1.
    intros. 
      assert (U3Hyp': forall b1 z, U3 b1 z = true -> L2 b1 = true \/ j23 b1 <> None).
      { intros. eapply (H1 b1 z). rewrite H3; trivial. }
      clear H1.
      destruct (MOD32 U3Hyp' _ _ H2). left; trivial. 
      destruct H1 as [? [? [? ?]]].
      right. exists x, x0. rewrite H3. split; trivial. }
  {
   (*inductive case*)
    remember (S x) as x'. simpl in H.
    rename st2' into st2''. rename m2' into m2''.
    destruct H as [st2' [m2' [U4 [U3 [Step2 [StepN2 HU]]]]]]. subst x'.
    destruct (effcore_diagram23 _ _ _ _ _ Step2 _ _ _ _ _ _ MC23) 
      as [c3' [m3' [d23' [j23' [L2a' [L3a' [InjInc23  
             [Gsep23 [LocAlloc23 [MC23' [U5 [Steps3 MOD23]]]]]]]]]]]]; clear effcore_diagram23.
    assert (FWD2: mem_forward m2 m2').
        eapply effstep_fwd; eassumption.
    assert (FWD2': mem_forward m2' m2'').
        eapply effstepN_fwd; eassumption.
    assert (FWD3: mem_forward m3 m3').
        destruct Steps3 as [[n K] | [[n K] _]];
             eapply effstepN_fwd; eassumption.
    destruct (IHx _ j23' d23' _ _ c3' m3' StepN2 _ _ MC23') 
        as [c3'' [m3'' [d23'' [j23'' [LL2 [LL3 [InjIncr' 
             [Gsep' [LocAlloc23' [MC23'' [U3' [StepN3 MOD23']]]]]]]]]]]]; clear IHx.
    assert (FWD3': mem_forward m3' m3'').
        destruct StepN3 as [[n K] | [[n K] _]];
             eapply effstepN_fwd; eassumption.
    exists c3''. exists m3''. exists d23''. exists j23'', LL2, LL3.
    split. { (*mini_intern_trans*) clear - InjIncr' InjInc23 LocAlloc23'.
             destruct InjIncr'; destruct InjInc23. destruct LocAlloc23'; subst.
             split. eapply inject_incr_trans; eassumption.
             intros. remember(j23' b1) as q.
             destruct q; symmetry in Heqq.
             + destruct p. specialize (H _ _ _ Heqq). rewrite J' in H. inv H.
               destruct (H2 _ _ _ J Heqq). rewrite H, H3; simpl. split; trivial.
             + apply (H0 _ _ _ Heqq J'). } 
    split. { clear - FWD2 InjIncr' InjInc23 Gsep' Gsep23.
             destruct InjIncr'; destruct InjInc23. 
             red; intros. remember(j23' b1) as q.
             destruct q; symmetry in Heqq.
             + destruct p. specialize (H _ _ _ Heqq). rewrite J' in H. inv H.
               apply (Gsep23 _ _ _ J Heqq). 
             + destruct (Gsep' _ _ _ Heqq J'). split; trivial. intros N. elim H3; clear H3. apply FWD2; eauto. }
    split. { specialize (freshblock_trans _ _ _ FWD2 FWD2'); intros FW2.
             specialize (freshblock_trans _ _ _ FWD3 FWD3'); intros FW3.
             clear - FW2 FW3 LocAlloc23 LocAlloc23'.
             destruct LocAlloc23; subst. destruct LocAlloc23'; subst.
             split; extensionality b. 
             + rewrite <- orb_assoc, FW2; trivial.
             + rewrite <- orb_assoc, FW3; trivial. }
    split. apply MC23''.
    exists (fun b z => U5 b z || (U3' b z && valid_block_dec m3 b)). 
    split. clear MOD23 MOD23'. 
           destruct Steps3; destruct StepN3.
           (*1/4*)
              left. eapply effstep_plus_trans; eassumption.
           (*2/4*)
              left. destruct H0 as [EFF3 CT].
              eapply effstep_plus_star_trans; eassumption. 
           (*3/4*)
               left. destruct H as [EFF3 CORD].
               eapply effstep_star_plus_trans; eassumption.
           (*4/4*)
               right. destruct H as [EFF3 CORD].
                      destruct H0 as [EFF3' CT].
               split. eapply effstep_star_trans; eassumption.
               eapply t_trans.
                 apply CT. clear CT.  
                 apply t_step.
                 constructor 2. apply CORD.
    (*MOD23-clause*) subst U2. intros U4Hyp b3 ofs HU3.
      apply orb_true_iff in HU3.
      destruct HU3.
      - assert (U4Hyp': forall b1 z, U4 b1 z = true -> L2 b1 = true \/ j23 b1 <> None).
        { intros. apply (U4Hyp b1 z). rewrite H0; trivial. }
        destruct (MOD23 U4Hyp' _ _ H). left; trivial.
        right. destruct H0 as [? [? [? ?]]]. exists x0, x1; rewrite H1; split; trivial.
      - apply andb_true_iff in H. destruct H.
         destruct (valid_block_dec m3 b3); try inv H0.
         assert (U3Hyp: forall b z, U3 b z = true -> L2a' b = true \/ j23' b <> None).
         { intros. 
           assert (U3valid:= effstepN_valid _ _ _ _ _ _ _ _ StepN2 _ _ H0).
           specialize (U4Hyp b z). rewrite H0 in U4Hyp; simpl in U4Hyp.
           destruct (valid_block_dec m2 b); simpl in U4Hyp.
           * rewrite orb_true_r in U4Hyp.
             destruct LocAlloc23; subst. 
             destruct U4Hyp; trivial.
             left. rewrite H1; trivial.
             right. remember (j23 b) as q. destruct q; try solve [congruence].
                    symmetry in Heqq; destruct p. destruct InjInc23 as [II _].
                    rewrite (II _ _ _ Heqq). discriminate.
           * rewrite orb_false_r in U4Hyp.
             destruct LocAlloc23. subst. left.
             assert (freshblockProp m2 m2' b) by (split; trivial).
             rewrite freshblock_asProp in H1. unfold asProp in H1; rewrite H1; apply orb_true_r. 
         }
         destruct (MOD23' U3Hyp _ _ H); clear MOD23'.
         * destruct LocAlloc23; subst.
           apply orb_true_iff in H0. destruct H0. left; trivial.
           apply freshblockProp_char in H0.
           destruct H0. contradiction.
         * destruct H0 as [? [? [? ?]]].
           destruct InjInc23 as [II23a II23b].
           remember (j23 x0) as q.
           destruct q; symmetry in Heqq.
           + destruct p; specialize (II23a _ _ _ Heqq). rewrite II23a in H0. inv H0.
             right. exists x0, x1. split; trivial. rewrite H1. simpl.
             destruct (match_valid23 _ _ _ _ _ _ _ _ MC23) as [A [ B C]].
             destruct (C _ _ _ Heqq). destruct (valid_block_dec m2 x0); try contradiction. apply orb_true_r.
           + destruct (II23b _ _ _ Heqq H0). destruct LocAlloc23; subst.
             apply orb_true_iff in H3. destruct H3. left; trivial.
             apply freshblockProp_char in H3.
             destruct H3; contradiction.
  }
+
  (*case 2*)
   inv CS2.
   assert (L2' = L2).
   { destruct LocAlloc12; subst. extensionality b. rewrite freshblock_irrefl; apply orb_false_r. }
   subst L2'. 
   exists st3. exists m3.
   exists (d12',Some st2',d23).
   exists  (compose_meminj j12' j23), L1', L3. 
   split. { destruct InjIncr12.
            split. eapply compose_meminj_inject_incr. eassumption. apply inject_incr_refl.
            intros b1 b3 d JJ JJ'.
            destruct (compose_meminjD_Some _ _ _ _ _ JJ') as [b2 [d1 [d2 [J12' [J23 D]]]]]. subst d; clear JJ'.
            destruct (compose_meminjD_None _ _ _ JJ).
            - destruct (H0 _ _ _ H1 J12'). split; trivial.
              destruct (match_wd23 _ _ _ _ _ _ _ _  MC23 _ _ _ J23); auto.
            - destruct H1 as [? [? [? ?]]].
              specialize (H _ _ _ H1). rewrite J12' in H; inv H. congruence. }
   split. { intros b1 b3 d J J'. 
            destruct (compose_meminjD_Some _ _ _ _ _ J') as [b2 [d1 [d2 [J12' [J23 D]]]]]. subst d; clear J'.
            destruct (compose_meminjD_None _ _ _ J); clear J.
            - destruct (Gsep _ _ _ H J12'); split; trivial. red in LocAlloc12.
              admit. (*complete when right genv conditins are added apply (senv.equiv? _ _ g2 g3); try assumption.*)
            - destruct H as [? [? [? ?]]]. destruct InjIncr12  as [II _].
              rewrite (II _ _ _ H) in J12'. inv J12'. congruence. }
   split. { destruct LocAlloc12 as [? _]; subst. split; trivial.
            extensionality b. rewrite freshblock_irrefl, orb_false_r; trivial. }
   split.
   { clear effcore_diagram23.
     exists st2'. exists m2'. exists j12'. exists j23, L2. repeat split; auto. 
       destruct (match_wd12 _ _ _ _ _ _ _ _ MC12' _ _ _ H0). trivial. 
       destruct InjIncr12 as [II12a II12b].
       remember (j12 b1) as w.
       destruct w; symmetry in Heqw.
       - destruct p. rewrite (II12a _ _ _ Heqw) in H0. inv H0. eapply (full _ _ _ _ Heqw).
       - destruct (II12b _ _ _ Heqw H0). congruence. }
    exists (fun b z => false). 
    split. right. split. exists O. simpl; auto.
    apply t_step. constructor 1; auto. intros; discriminate.
Unshelve. destruct LocAlloc12 as [? _]; subst.
    destruct (L1 b1); trivial; congruence.
Admitted. (*OK, apart from the two 'intentional' admits.*)

End CoreDiagrams_trans.