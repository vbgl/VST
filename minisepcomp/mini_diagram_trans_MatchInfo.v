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

Require Import minisepcomp.mini_simulations_MatchInfo.
Require Import minisepcomp.mini_simulations_lemmas_MatchInfo.

Ltac exact_eq H :=
  revert H;
  match goal with
    |- ?p -> ?q => cut (p = q); [intros ->; auto | ]
  end.

Lemma EQTRIV {A B: Type} (f g : A -> B) (H: f = g) a: f a = g a.
Proof. subst; trivial. Qed.

Lemma freshblock_forward m1 m2 m3 b: mem_forward m2 m3 -> freshblock m1 m2 b = true -> freshblock m1 m3 b = true.
Proof. intros. apply freshblockProp_char. apply freshblockProp_char in H0.
  destruct H0. split; trivial.
  apply H; trivial.
Qed. 

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
(core_data12 : Type)
(match_core12 : core_data12 -> C1 -> mem -> MatchInfoE -> C2 -> mem -> Prop)
(core_ord12 : core_data12 -> core_data12 -> Prop)
(senvs_dom_eq12 : Senv.equiv g1 g2 /\ genv_next_eq g1 g2)
(match_wd12 : forall (d : core_data12) (c1 : C1) (m1 : mem) (M1 : block -> Z -> bool)
               (L : block -> bool) (M2 : block -> Z -> bool) (c2 : C2) 
               (m2 : mem),
             match_core12 d c1 m1 (M1, L, M2) c2 m2 ->
             forall b : block, L b = true -> Mem.valid_block m1 b /\ Mem.valid_block m2 b)
(effcore_diagram12 : forall (st1 : C1) (m1 : mem) (st1' : C1) (m1' : mem)
                      (U1 : block -> Z -> bool),
                    effstep Sem1 g1 U1 st1 m1 st1' m1' ->
                    forall (cd : core_data12) (st2 : C2) (m2 : mem) 
                      (M1 : block -> Z -> bool) (L : block -> bool) 
                      (M2 : block -> Z -> bool),
                    match_core12 cd st1 m1 (M1, L, M2) st2 m2 ->
                    exists
                      (st2' : C2) (m2' : mem) (cd' : core_data12) (U2 : block -> Z -> bool),
                      (effstep_plus Sem2 g2 U2 st2 m2 st2' m2' \/
                       effstep_star Sem2 g2 U2 st2 m2 st2' m2' /\ core_ord12 cd' cd) /\
                      (let L' := fun b : block => L b || freshblock m1 m1' b in
                       let M1' :=
                         fun (b : block) (z : Z) =>
                         valid_block_dec m1 b && negb (L b) && (M1 b z || U1 b z) in
                       let M2' :=
                         fun (b : block) (z : Z) =>
                         valid_block_dec m2 b && negb (L b) && (M2 b z || U2 b z) in
                       L' = (fun b : block => L b || freshblock m2 m2' b) /\
                       match_core12 cd' st1' m1' (M1', L', M2') st2' m2'))
(core_data23 : Type)
(match_core23 : core_data23 ->
               meminj -> MatchInfo -> C2 -> mem -> MatchInfo -> C3 -> mem -> Prop)
(core_ord23 : core_data23 -> core_data23 -> Prop)
(match_wd23 : forall (d : core_data23) (j : meminj) (M1 : block -> Z -> bool)
               (L1 : block -> bool) (c1 : C2) (m1 : mem) (M2 : block -> Z -> bool)
               (L2 : block -> bool) (c2 : C3) (m2 : mem),
             match_core23 d j (M1, L1) c1 m1 (M2, L2) c2 m2 ->
             forall (b1 b2 : block) (d0 : Z), j b1 = Some (b2, d0) -> L1 b1 = L2 b2)
(match_valid23 : forall (d : core_data23) (j : meminj) (E1 : MatchInfo) 
                  (c1 : C2) (m1 : mem) (E2 : MatchInfo) (c2 : C3) (m2 : mem),
                match_core23 d j E1 c1 m1 E2 c2 m2 -> meminj_valid j E1 E2 m1 m2)
(effcore_diagram23 : forall (st1 : C2) (m1 : mem) (st1' : C2) (m1' : mem)
                      (U1 : block -> Z -> bool),
                    effstep Sem2 g2 U1 st1 m1 st1' m1' ->
                    forall (cd : core_data23) (st2 : C3) (j : meminj) 
                      (m2 : mem) (E1 E2 : MatchInfo),
                    match_core23 cd j E1 st1 m1 E2 st2 m2 ->
                    exists
                      (st2' : C3) (m2' : mem) (cd' : core_data23) (j' : meminj) 
                    (U2 : block -> Z -> bool),
                      (effstep_plus Sem3 g3 U2 st2 m2 st2' m2' \/
                       effstep_star Sem3 g3 U2 st2 m2 st2' m2' /\ core_ord23 cd' cd) /\
                      (let (M1, L1) := E1 in
                       let (M2, L2) := E2 in
                       let L1' := fun b : block => L1 b || freshblock m1 m1' b in
                       let L2' := fun b : block => L2 b || freshblock m2 m2' b in
                       let M1' :=
                         fun (b : block) (z : Z) =>
                         valid_block_dec m1 b && negb (L1 b) && (M1 b z || U1 b z) in
                       let M2' :=
                         fun (b : block) (z : Z) =>
                         valid_block_dec m2 b && negb (L2 b) && (M2 b z || U2 b z) in
                       mini_intern_incr j j' L1' L2' /\
                       globals_separate m1 g3 j j' /\
                       match_core23 cd' j' (M1', L1') st1' m1' (M2', L2') st2' m2'))
(st1 : C1) (m1 m2 m3 m1': mem) (st1' : C1)
(U1 : block -> Z -> bool)
(CS1 : effstep Sem1 g1 U1 st1 m1 st1' m1')
(d12 : core_data12)
(d23 : core_data23)
(st3 : C3)
(j : meminj)
(M1 M2 M3 : block -> Z -> bool)
(L1 L3 : block -> bool)
(c2 : C2)
(MC12 : match_core12 d12 st1 m1 (M1, L1, M2) c2 m2)
(MC23 : match_core23 d23 j (M2, L1) c2 m2 (M3, L3) st3 m3),
exists
  (st2' : C3) (m2' : mem) (cd' : core_data12 * option C2 * core_data23) 
(j' : meminj) (U2 : block -> Z -> bool),
  (effstep_plus Sem3 g3 U2 st3 m3 st2' m2' \/
   effstep_star Sem3 g3 U2 st3 m3 st2' m2' /\
   clos_trans (core_data12 * option C2 * core_data23)
     (sem_compose_ord_eq_eq core_ord12 core_ord23 C2) cd' (d12, Some c2, d23)) /\
  (let L1' := fun b : block => L1 b || freshblock m1 m1' b in
   let L2' := fun b : block => L3 b || freshblock m3 m2' b in
   let M1' :=
     fun (b : block) (z : Z) => valid_block_dec m1 b && negb (L1 b) && (M1 b z || U1 b z) in
   let M2' :=
     fun (b : block) (z : Z) => valid_block_dec m3 b && negb (L3 b) && (M3 b z || U2 b z) in
   mini_intern_incr j j' L1' L2' /\
   globals_separate m1 g3 j j' /\
   (let (y, d2) := cd' in
    let (d1, X) := y in
    exists (c0 : C2) (m0 : mem) (M0 : block -> Z -> bool),
      X = Some c0 /\
      match_core12 d1 st1' m1' (M1', L1', M0) c0 m0 /\
      match_core23 d2 j' (M0, L1') c0 m0 (M2', L2') st2' m2')).
(*
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
         j b1 = Some (b2, delta) /\ U1 b1 (ofs - delta) = true))).*)
Proof. intros.
  exploit effcore_diagram12. apply CS1. apply MC12.
  intros [st2' [m2' [d12' [U2 [STEPS2 [HL' MC12']]]]]]; clear effcore_diagram12.  
  assert (ZZ: effstep_plus Sem2 g2 U2 c2 m2 st2' m2' \/
    (c2,m2) = (st2',m2') /\ U2 = (fun b z => false) /\ core_ord12 d12' d12).
  { destruct STEPS2. auto.
    destruct H.
    destruct H. destruct x.
    right. simpl in H. destruct H. split; auto.
    left. exists x; auto. }
  clear STEPS2. destruct ZZ as [CS2 | [CS2 [HU2 ord12']]].
 (*case1*) 
+ destruct CS2.
  clear CS1. 
  cut (exists st3' : C3,  exists m3' : mem, 
    exists d23':core_data23, exists j', exists U3,
      (effstep_plus Sem3 g3 U3 st3 m3 st3' m3' \/
        (effstep_star Sem3 g3 U3 st3 m3 st3' m3' /\
        clos_trans (core_data12 * option C2 * core_data23)
        (sem_compose_ord_eq_eq core_ord12 core_ord23 C2) 
               (d12', Some st2', d23')
        (d12, Some c2,d23)))
    /\ let L2' := fun b : block => L1 b || freshblock m2 m2' b in
       let L3' := fun b : block => L3 b || freshblock m3 m3' b in
       let M2' := (fun b z => valid_block_dec m2 b && negb (L1 b) && (M2 b z || U2 b z)) in
       let M3' := (fun b z => valid_block_dec m3 b && negb (L3 b) && (M3 b z || U3 b z)) in
      mini_intern_incr j j' L2' L3' 
    /\  globals_separate m2 g3 j j'
    (*/\mini_locally_allocated L1 L3 m2 m3 L22' L3' m2' m3'*)
    /\ match_core23 d23' j' (M2',L2') st2' m2' (M3',L3') st3' m3').    
(*  cut (exists st3' : C3,  exists m3' : mem, 
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
         j b2 = Some (b3, delta) /\ U2 b2 (ofs - delta) = true)))).*)

  - intros [st3' [m3' [d23' [j' [U3 [STEP3 (*[INV'*) [InjIncr23
          [Gsep23 MC23']]]]]]]]. 
    exists st3'. exists m3'. 
    exists (d12', Some st2', d23').
    exists j', U3.
    split. assumption.
    split. { destruct InjIncr23 as [INC23a INC23b].
      split; trivial.
      intros b2 b3 d; intros.
        destruct (INC23b _ _ _ J J'). split; trivial.
        rewrite (EQTRIV _ _ HL'); trivial. }
    split. { red; intros. destruct (Gsep23 _ _ _ J J'); clear Gsep23. split; trivial.
             intros N. elim H0; clear H0. destruct InjIncr23 as [INC SEP].
             destruct (SEP _ _ _ J J').
             assert ((fun b : block => L1 b || freshblock m1 m1' b) b1 = true). rewrite (EQTRIV _ _ HL'); trivial.
             simpl in H3.
             case_eq (L1 b1); intros ZZ; rewrite ZZ in *; simpl in  *. eapply match_wd12; eauto.
             apply freshblockProp_char in H3. destruct H3; congruence. }
    exists st2', m2'; eexists. split. trivial. rewrite <- HL' in MC23'. split; eassumption.
  -  
  clear MC12 MC12' HL'.
  clear st1 m1 st1' m1'. 
  clear senvs_dom_eq12 match_wd12 C1 Sem1 match_core12 g1 U1 M1. 
  revert U2 j d23 c2 m2 st3 m3 H M2 L1 M3 L3 MC23. 
  induction x; intros. 
  {
   (*base case*) simpl in H.
    destruct H as [st2 [m2'' [U3 [U4 [? [[? ?] ?]]]]]]. subst U4. simpl in H2.
    assert (U2 = U3). { subst U2. extensionality b. extensionality z. apply orb_false_r. }
    clear H2. subst U2. inv H0. simpl in *. 
    exploit effcore_diagram23. apply H. apply MC23.
    intros [st3' [m3' [d23' [j23' [U5 [STEPS3 [InjIncr23 
          [Gsep23 MC23' ]]]]]]]]; clear effcore_diagram23.
    exists st3'. exists m3'. exists d23', j23', U5. 
    split. { destruct STEPS3. left; assumption.
             destruct H0. right. split; trivial.
             apply t_step. constructor 2. apply H1. }
    split. trivial. 
    split; trivial. }
  {
   (*inductive case*)
    remember (S x) as x'. simpl in H.
    rename st2' into st2''. rename m2' into m2''.
    destruct H as [st2' [m2' [U4 [U3 [Step2 [StepN2 HU]]]]]]. subst x'.
    exploit effcore_diagram23. apply Step2. apply MC23.
    intros [c3' [m3' [d23' [j23' [U5 [Steps3 [InjInc23  
             [Gsep23  MC23']]]]]]]]; clear effcore_diagram23.
    assert (FWD2: mem_forward m2 m2').
        eapply effstep_fwd; eassumption.
    assert (FWD2': mem_forward m2' m2'').
        eapply effstepN_fwd; eassumption.
    assert (FWD3: mem_forward m3 m3').
        destruct Steps3 as [[n K] | [[n K] _]];
             eapply effstepN_fwd; eassumption.
    exploit (IHx _ j23' d23' _ _ c3' m3' StepN2). apply MC23'. 
    intros [c3'' [m3'' [d23'' [j23'' [U3' [StepN3 [InjIncr' 
             [Gsep' MC23'']]]]]]]]; clear IHx.
    assert (FWD3': mem_forward m3' m3'').
        destruct StepN3 as [[n K] | [[n K] _]];
             eapply effstepN_fwd; eassumption.
    exists c3'', m3'', d23'', j23''. 
    exists (fun b z => U5 b z || (U3' b z && valid_block_dec m3 b)).
    split. { destruct Steps3; destruct StepN3.
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
                 constructor 2. apply CORD. }
   split. { (*mini_intern_trans*) clear - InjIncr' InjInc23 FWD3' FWD3 FWD2' FWD2.
             destruct InjIncr'; destruct InjInc23. 
             split. eapply inject_incr_trans; eassumption.
             intros. case_eq (j23' b1); intros.
             + destruct p. specialize (H _ _ _ H3). rewrite J' in H. inv H.
               destruct (H2 _ _ _ J H3).
               split.
               - case_eq (L1 b1); intros Lb; rewrite Lb in *; simpl in *; trivial.
                 eapply freshblock_forward; eassumption. 
               - case_eq (L3 b); intros Lb; rewrite Lb in *; simpl in *; trivial.
                 eapply freshblock_forward; eassumption.
             + destruct (H0 _ _ _ H3 J').
               split.
               - case_eq (L1 b1); intros Lb; rewrite Lb in *; simpl in *; trivial.
                 erewrite <- freshblock_trans; eassumption. 
               - case_eq (L3 b2); intros Lb; rewrite Lb in *; simpl in *; trivial.
                 erewrite <- freshblock_trans; eassumption. } 
    split. { clear - InjIncr' InjInc23 Gsep' Gsep23 FWD2.
             destruct InjIncr'; destruct InjInc23. 
             red; intros. remember(j23' b1) as q.
             destruct q; symmetry in Heqq.
             + destruct p. specialize (H _ _ _ Heqq). rewrite J' in H. inv H.
               apply (Gsep23 _ _ _ J Heqq). 
             + destruct (Gsep' _ _ _ Heqq J'). split; trivial.
               intros N. elim H3; clear H3. apply FWD2; eauto. }
    exact_eq MC23''; subst U2. f_equal.
    + f_equal.
      - extensionality bb. extensionality z.
        case_eq (L1 bb); simpl; intros.
        * repeat rewrite andb_false_r; simpl; trivial.
        * rewrite andb_true_r.
          case_eq (valid_block_dec m2 bb); simpl; intros.
          ++ rewrite andb_true_r, orb_assoc.
             case_eq (valid_block_dec m2' bb); simpl; intros.
             2: elim n; apply FWD2; trivial.
             assert (FR2: freshblock m2 m2' bb = false). apply freshblock_charF; left; trivial.
             rewrite FR2; simpl. trivial.
          ++ case_eq (U3 bb z); simpl; intros. 2: rewrite andb_false_r; trivial.
             assert (Mem.valid_block m2' bb). 
             { eapply effstepN_valid. apply StepN2. apply H1. }
             case_eq (valid_block_dec m2' bb); simpl; intros; try contradiction.
             assert (FR2: freshblock m2 m2' bb = true). eapply freshblockProp_char. split; trivial.
             rewrite FR2; simpl; trivial.
      - extensionality bb. rewrite <- (freshblock_trans m2 m2' m2''), orb_assoc; trivial.
    + f_equal.
      - extensionality bb. extensionality z.
        case_eq (L3 bb); simpl; intros.
        * repeat rewrite andb_false_r; simpl; trivial.
        * rewrite andb_true_r.
          case_eq (valid_block_dec m3 bb); simpl; intros.
          ++ rewrite andb_true_r, orb_assoc.
             case_eq (valid_block_dec m3' bb); simpl; intros.
             2: elim n; apply FWD3; trivial.
             assert (FR3: freshblock m3 m3' bb = false). apply freshblock_charF; left; trivial.
             rewrite FR3; simpl. trivial.
          ++ case_eq (U3' bb z); simpl; intros. 2: rewrite andb_false_r; trivial.
             assert (Mem.valid_block m3' bb). 
             { destruct StepN3 as [[nn StepNN] | [[nn StepNN] _]]; eapply effstepN_valid.
               apply StepNN. eassumption. apply StepNN. eassumption. }
             case_eq (valid_block_dec m3' bb); simpl; intros; try contradiction.
             assert (FR3: freshblock m3 m3' bb = true). eapply freshblockProp_char. split; trivial.
             rewrite FR3; simpl; trivial.
      - extensionality bb. rewrite <- (freshblock_trans m3 m3' m3''), orb_assoc; trivial.
  }
+
  (*case 2*)
   inversion CS2; clear CS2. subst st2' m2' U2.  
   exists st3, m3, (d12',Some c2,d23), j, (fun b z => false). 
   split. { right. split. exists O. simpl; auto.
            apply t_step. constructor 1; auto. }
   split. { split; intros. apply inject_incr_refl. congruence. }
   split. { red; intros; congruence. }
   exists c2, m2. eexists. split. trivial.
   split. eassumption.
   exploit match_valid23. apply MC23. intros MV.
   exact_eq MC23. f_equal.
       - f_equal.
         * extensionality b. extensionality z. rewrite orb_false_r.
           destruct MV as [MVa [MVb [MVc [MVd MVe]]]].
           case_eq (M2 b z); simpl; intros.
           -- destruct (MVd _ _ H) as [X Y]; rewrite Y; simpl.
             destruct (valid_block_dec m2 b); trivial. contradiction.
           -- rewrite andb_false_r; trivial.
         * rewrite HL'. extensionality b. rewrite freshblock_irrefl', orb_false_r; trivial. 
       - f_equal; extensionality b.
         -- extensionality z. rewrite orb_false_r.
            destruct MV as [MVa [MVb [MVc [MVd MVe]]]].
            case_eq (M3 b z); simpl; intros.
            ++ destruct (MVe _ _ H) as [X Y]; rewrite Y; simpl.
               destruct (valid_block_dec m3 b); trivial. contradiction.
            ++ rewrite andb_false_r; trivial.
         -- rewrite freshblock_irrefl, orb_false_r; trivial.
Qed.

Lemma effcore_diagram_trans: forall
(core_data12 : Type)
(match_core12 : core_data12 -> meminj ->
               MatchInfo -> C1 -> mem -> MatchInfo -> C2 -> mem -> Prop)
(core_ord12 : core_data12 -> core_data12 -> Prop)
(match_valid12 : forall d j E1 c1 m1 E2 c2 m2 (MS: match_core12 d j E1 c1 m1 E2 c2 m2),
    meminj_valid j E1 E2 m1 m2)
(match_wd12: forall d j M1 L1 c1 m1 M2 L2 c2 m2
   (MS: match_core12 d j (M1,L1) c1 m1 (M2,L2) c2 m2)
    b1 b2 d (J:j b1=Some(b2, d)), L1 b1 = L2 b2)
(effcore_diagram12 : 
    forall st1 m1 st1' m1' U1, 
    effstep Sem1 g1 U1 st1 m1 st1' m1' ->
    forall cd st2 j m2 E1 E2,
    match_core12 cd j E1 st1 m1 E2 st2 m2 ->
    exists st2', exists m2', exists cd', exists j', exists U2,              
      ((effstep_plus Sem2 g2 U2 st2 m2 st2' m2' \/
       (effstep_star Sem2 g2 U2 st2 m2 st2' m2' /\ core_ord12 cd' cd)) /\
       match E1, E2 with (M1,L1), (M2, L2) =>
         let L1' := (fun b : block => L1 b || freshblock m1 m1' b) in
         let L2' := (fun b : block => L2 b || freshblock m2 m2' b) in
         let M1' := (fun b z => valid_block_dec m1 b && negb (L1 b) && (M1 b z || U1 b z)) in
         let M2' := (fun b z => valid_block_dec m2 b && negb (L2 b) && (M2 b z || U2 b z)) in
         mini_intern_incr j j' L1' L2'
      /\ globals_separate m1 g2 j j' 
      /\ match_core12 cd' j' (M1',L1') st1' m1' (M2',L2') st2' m2'
       end))
(core_data23 : Type)
(match_core23 : core_data23 -> meminj ->
               MatchInfo -> C2 -> mem -> MatchInfo -> C3 -> mem -> Prop)
(core_ord23 : core_data23 -> core_data23 -> Prop)
(*(genvs_dom_eq23 : genvs_domain_eq g2 g3)*)
(match_genv23 : forall (d : core_data23) (j : meminj) E1 
                 (c1 : C2) (m1 : mem) E2 
                 (c2 : C3) (m2 : mem),
               match_core23 d j E1 c1 m1 E2 c2 m2 ->
               meminj_preserves_globals g2 j /\
               (forall b : block, isGlobalBlock g2 b = true -> j b <> None))
(match_valid23 : forall d j E1 c1 m1 E2 c2 m2 (MS: match_core23 d j E1 c1 m1 E2 c2 m2),
    meminj_valid j E1 E2 m1 m2)
(match_wd23: forall d j M1 L1 c1 m1 M2 L2 c2 m2
   (MS: match_core23 d j (M1,L1) c1 m1 (M2,L2) c2 m2)
    b1 b2 d (J:j b1=Some(b2, d)), L1 b1 = L2 b2)
(effcore_diagram23 : 
    forall st1 m1 st1' m1' U1, 
    effstep Sem2 g2 U1 st1 m1 st1' m1' ->
    forall cd st2 j m2 E1 E2,
    match_core23 cd j E1 st1 m1 E2 st2 m2 ->
    exists st2', exists m2', exists cd', exists j', exists U2,              
      ((effstep_plus Sem3 g3 U2 st2 m2 st2' m2' \/
       (effstep_star Sem3 g3 U2 st2 m2 st2' m2' /\ core_ord23 cd' cd)) /\
       match E1, E2 with (M1,L1), (M2, L2) =>
         let L1' := (fun b : block => L1 b || freshblock m1 m1' b) in
         let L2' := (fun b : block => L2 b || freshblock m2 m2' b) in
         let M1' := (fun b z => valid_block_dec m1 b && negb (L1 b) && (M1 b z || U1 b z)) in
         let M2' := (fun b z => valid_block_dec m2 b && negb (L2 b) && (M2 b z || U2 b z)) in
         mini_intern_incr j j' L1' L2'
      /\ globals_separate m1 g3 j j' 
      /\ match_core23 cd' j' (M1',L1') st1' m1' (M2',L2') st2' m2'
       end))
  st1 m1 st1' m1' (U1 : block -> Z -> bool)
  (CS1 : effstep Sem1 g1 U1 st1 m1 st1' m1')
  d12 d23 st3 m3 
  (E1 E2 E3 : MatchInfo)
  c2 m2
  (j12 j23 : meminj)
  (MC12 : match_core12 d12 j12 E1 st1 m1 E2 c2 m2)
  (MC23 : match_core23 d23 j23 E2 c2 m2 E3 st3 m3)
  (full : full_ext j12 j23 (snd E1) (snd E2)), 
exists
  (st2' : C3) (m2' : mem) (cd' : core_data12 * option C2 * core_data23) 
(j' : meminj) (U2 : block -> Z -> bool),
  (effstep_plus Sem3 g3 U2 st3 m3 st2' m2' \/
   effstep_star Sem3 g3 U2 st3 m3 st2' m2' /\
   clos_trans (core_data12 * option C2 * core_data23)
     (sem_compose_ord_eq_eq core_ord12 core_ord23 C2) cd' (d12, Some c2, d23)) /\
  (let (M1, L1) := E1 in
   let (M2, L0) := E3 in
   let L1' := fun b : block => L1 b || freshblock m1 m1' b in
   let L2' := fun b : block => L0 b || freshblock m3 m2' b in
   let M1' :=
     fun (b : block) (z : Z) => valid_block_dec m1 b && negb (L1 b) && (M1 b z || U1 b z)
     in
   let M2' :=
     fun (b : block) (z : Z) => valid_block_dec m3 b && negb (L0 b) && (M2 b z || U2 b z)
     in
   mini_intern_incr (compose_meminj j12 j23) j' L1' L2' /\
   globals_separate m1 g3 (compose_meminj j12 j23) j' /\
   (let (y, d2) := cd' in
    let (d1, X) := y in
    exists (c0 : C2) (m0 : mem) (j1 j2 : meminj) (E2' : MatchInfo),
      X = Some c0 /\
      j' = compose_meminj j1 j2 /\
      match_core12 d1 j1 (M1', L1') st1' m1' E2' c0 m0 /\
      match_core23 d2 j2 E2' c0 m0 (M2', L2') st2' m2' /\
      full_ext j1 j2 (snd (M1', L1')) (snd E2'))).
Proof. intros. 
  exploit (effcore_diagram12 _ _ _ _ _ CS1). eapply MC12. 
  intros [st2' [m2' [d12' [j12' [U2 [STEPS2 Y]]]]]]; clear effcore_diagram12.
  destruct E1 as [M1 L1]. destruct E2 as [M2 L2]. 
  assert (ZZ: effstep_plus Sem2 g2 U2 c2 m2 st2' m2' \/
    (c2,m2) = (st2',m2') /\ (U2 = fun b z => false) /\ core_ord12 d12' d12).
  { clear Y MC12 MC23. destruct STEPS2. auto.
    destruct H.
    destruct H. destruct x.
    right. simpl in H. destruct H. split. trivial. split; trivial.
    left. exists x; auto. }
  destruct Y as [INC12 [Gsep12 MATCH12']].
  clear STEPS2. destruct ZZ as [CS2 | [CS2 [HU2 ord12']]].
 (*case1*) 
+ destruct CS2.
  clear CS1. destruct E3 as [M3 L3].
  cut (exists st3' : C3,  exists m3' : mem, 
    exists d23':core_data23, exists j23', exists U3,
      (effstep_plus Sem3 g3 U3 st3 m3 st3' m3' \/
        (effstep_star Sem3 g3 U3 st3 m3 st3' m3' /\
        clos_trans (core_data12 * option C2 * core_data23)
        (sem_compose_ord_eq_eq core_ord12 core_ord23 C2) 
               (d12', Some st2', d23')
        (d12, Some c2,d23)))
    /\ let L2' := fun b : block => L2 b || freshblock m2 m2' b in
       let L3' := fun b : block => L3 b || freshblock m3 m3' b in
       let M2' := (fun b z => valid_block_dec m2 b && negb (L2 b) && (M2 b z || U2 b z)) in
       let M3' := (fun b z => valid_block_dec m3 b && negb (L3 b) && (M3 b z || U3 b z)) in
       mini_intern_incr j23 j23' L2' L3'
      /\ globals_separate m2 g3 j23 j23' 
      /\ match_core23 d23' j23' (M2',L2') st2' m2' (M3',L3') st3' m3').
(*
E22', exists E3',
      mini_intern_incr j23 j23' L22' L3' /\
      globals_separate m2 g3 j23 j23' /\
(*    mini_locally_allocated L2 L3 m2 m3 L22' L3' m2' m3' /\*)
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
         j23 b2 = Some (b3, delta) /\ U2 b2 (ofs - delta) = true)))).*)
  - intros [st3' [m3' [d23' [j23' [U3 [STEP3 P3]]]]]]. (* L3' (*[INV'*) [InjIncr23 
          [Gsep23 [LocAlloc23 [MC23' [U3 [ZZ MOD23]]]]]]]]]]]].*)
    exists st3'. exists m3'. 
    exists (d12', Some st2', d23').
    exists (compose_meminj j12' j23'), U3.
    split. trivial.
    destruct P3 as [INC23 [GSep23 MATCH23']].
    split.
    { destruct INC12 as [INC12a INC12b]. destruct INC23 as [INC23a INC23b].
      split.
      + apply compose_meminj_inject_incr; eassumption.
      + intros b1 b3 d; intros.
        destruct (compose_meminjD_Some _ _ _ _ _ J') as [b2 [d1 [d2 [map12' [map23' extra]]]]]. subst d; clear J'.   
        destruct (compose_meminjD_None _ _ _ J) as [map12| [b2' [d [map12 map23]]]].
        * destruct (INC12b _ _ _ map12 map12'). split; trivial.
          case_eq (j23 b2).
          - intros [bb dd] J23. rewrite (INC23a _ _ _ J23) in map23'; inv map23'.
            apply orb_true_iff in H1. destruct H1.
              rewrite (match_wd23 _ _ _ _ _ _ _ _ _ _ MC23 _ _ _ J23) in H1; rewrite H1; trivial.
            apply freshblockProp_char in H1. destruct H1. elim H2; clear -J23 MC23 match_valid23.
            destruct (match_valid23 _ _ _ _ _ _ _ _ MC23) as [_ [_ [X _]]]. apply (X _ _ _ J23).
          - intros J23. destruct (INC23b _ _ _ J23 map23'); trivial.
        * rewrite (INC12a _ _ _ map12) in map12'. inv map12'.
          destruct (INC23b _ _ _ map23 map23'). split; trivial.
          case_eq (L1 b1); intros HH; trivial; simpl.
          rewrite (match_wd12 _ _ _ _ _ _ _ _ _ _ MC12 _ _ _ map12) in HH. rewrite HH in H0; simpl in H0.
          apply freshblockProp_char in H0. destruct H0.
          elim H2. destruct (match_valid12 _ _ _ _ _ _ _ _ MC12) as [_ [_ [X _]]]. apply (X _ _ _ map12). }
    split.
    { intros b1 b3 d; intros.
       destruct (compose_meminjD_Some _ _ _ _ _ J') as [b2 [d1 [d2 [map12' [map23' extra]]]]]. subst d; clear J'.
       destruct (compose_meminjD_None _ _ _ J) as [map12| [b2' [d [map12 map23]]]].
       * destruct (Gsep12 _ _ _ map12 map12'). split; trivial.
         admit. 
       * assert (HH: j12' b1 = Some (b2', d))
         by (eapply INC12; auto).
         rewrite HH in map12'. inv map12'. 
         (*eapply Gsep23; eauto. *) destruct (GSep23 _ _ _ map23 map23'). split; trivial.
         intros N. apply H0; clear H0.
         exploit match_valid12; try eapply MC12. intros [_ [_ [Z3 _]]]. apply (Z3 _ _ _ map12). 
    }
    exists st2', m2', j12', j23'. simpl in *. eexists. split; trivial. split; trivial.
         split. eassumption. simpl.
         split. trivial. red; intros. clear MATCH23' H STEP3.
         split. rewrite (match_wd12 _ _ _ _ _ _ _ _ _ _ MATCH12' _ _ _ H1) in H0; trivial.
         destruct INC12 as [INC12a INC12b]. 
         destruct INC23 as [INC23a INC23b]. 
         case_eq (j12 b1); intros.
         destruct p. rewrite (INC12a _ _ _ H) in H1; inv H1.
                     apply orb_false_iff in H0. destruct H0. 
                     red in full. destruct (full _ _ _ H0 H) as [HL2 [bb [dd J23]]].
                     rewrite (INC23a _ _ _ J23). eexists; eexists; reflexivity.
         destruct (INC12b _ _ _ H H1) as [X _]; rewrite X in *; discriminate.
  -  
  clear MC12 INC12 Gsep12 MATCH12' (*MatchHyp12*) full (*LocAlloc12 MOD12*) match_valid12 match_wd12. 
  clear st1 m1 st1' m1' j12 j12'. 
  clear C1 Sem1 match_core12 g1.
  revert U2 j23 d23 c2 m2 st3 m3 H L2 L3 M2 M3 MC23. 
  induction x; intros. 
  {
   (*base case*) simpl in H.
    destruct H as [st2 [m2'' [U3 [U4 [? [? ?]]]]]].
    destruct H0. inv H0; simpl in *.
    exploit effcore_diagram23. apply H. apply MC23.
    intros [st3' [m3' [d23' [j23' [U5 [STEP3 [InjIncr23 
          [Gsep23 MC23']]]]]]]]; clear effcore_diagram23.
    exists st3'. exists m3'. exists d23'. exists j23', U5. 
    split. destruct STEP3. left; assumption.
           destruct H0. right. split; trivial.
           apply t_step. constructor 2. apply H1. 
    split. trivial. 
    split. trivial.
    exact_eq MC23'. f_equal. f_equal. extensionality bb. extensionality z. rewrite orb_false_r; trivial. }
  {
   (*inductive case*)
    remember (S x) as x'. simpl in H.
    rename st2' into st2''. rename m2' into m2''.
    destruct H as [st2' [m2' [U4 [U3 [Step2 [StepN2 HU]]]]]]. subst x'.
    exploit effcore_diagram23. apply Step2. apply MC23.
    intros [c3' [m3' [d23' [j23' [U5 [Steps3 [InjInc23  
             [Gsep23 MC23']]]]]]]]; clear effcore_diagram23.
    assert (FWD2: mem_forward m2 m2').
        eapply effstep_fwd; eassumption.
    assert (FWD2': mem_forward m2' m2'').
        eapply effstepN_fwd; eassumption.
    assert (FWD3: mem_forward m3 m3').
        destruct Steps3 as [[n K] | [[n K] _]];
             eapply effstepN_fwd; eassumption.
    specialize (IHx _ j23' d23' _ _ c3' m3' StepN2 _ _ _ _ MC23').
    destruct IHx as [c3'' [m3'' [d23'' [j23'' [U3' [StepN3 [InjIncr' 
             [Gsep' MC23'']]]]]]]]. 
    assert (FWD3': mem_forward m3' m3'').
        destruct StepN3 as [[n K] | [[n K] _]];
             eapply effstepN_fwd; eassumption.
    exists c3''. exists m3''. exists d23''. exists j23'', (fun b z => U5 b z || (U3' b z && valid_block_dec m3 b)). 
    split. { 
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
                 constructor 2. apply CORD. }
    split. { (*mini_intern_trans*) clear - InjIncr' InjInc23 FWD2 FWD2' FWD3 FWD3'.
             destruct InjIncr'; destruct InjInc23.
             split. eapply inject_incr_trans; eassumption.
             intros. remember(j23' b1) as q.
             destruct q; symmetry in Heqq.
             + destruct p. specialize (H _ _ _ Heqq). rewrite J' in H. inv H.
               destruct (H2 _ _ _ J Heqq).
               split.
               - case_eq (L2 b1); intros Lb; rewrite Lb in *; simpl in *; trivial.
                 eapply freshblock_forward; eassumption. 
               - case_eq (L3 b); intros Lb; rewrite Lb in *; simpl in *; trivial.
                 eapply freshblock_forward; eassumption.
             + destruct (H0 _ _ _ Heqq J'). 
               split.
               - case_eq (L2 b1); intros Lb; rewrite Lb in *; simpl in *; trivial.
                 erewrite <- freshblock_trans; eassumption. 
               - case_eq (L3 b2); intros Lb; rewrite Lb in *; simpl in *; trivial.
                 erewrite <- freshblock_trans; eassumption. } 
    split. { clear - FWD2 InjIncr' InjInc23 Gsep' Gsep23.
             destruct InjIncr'; destruct InjInc23. 
             red; intros. remember(j23' b1) as q.
             destruct q; symmetry in Heqq.
             + destruct p. specialize (H _ _ _ Heqq). rewrite J' in H. inv H.
               apply (Gsep23 _ _ _ J Heqq). 
             + destruct (Gsep' _ _ _ Heqq J'). split; trivial. intros N. elim H3; clear H3. apply FWD2; eauto. }
    exact_eq MC23''; subst U2. f_equal.
    + f_equal.
      - extensionality bb. extensionality z.
        case_eq (L2 bb); simpl; intros.
        * repeat rewrite andb_false_r; simpl; trivial.
        * rewrite andb_true_r.
          case_eq (valid_block_dec m2 bb); simpl; intros.
          ++ rewrite andb_true_r, orb_assoc.
             case_eq (valid_block_dec m2' bb); simpl; intros.
             2: elim n; apply FWD2; trivial.
             assert (FR2: freshblock m2 m2' bb = false). apply freshblock_charF; left; trivial.
             rewrite FR2; simpl. trivial.
          ++ case_eq (U3 bb z); simpl; intros. 2: rewrite andb_false_r; trivial.
             assert (Mem.valid_block m2' bb). 
             { eapply effstepN_valid. apply StepN2. apply H1. }
             case_eq (valid_block_dec m2' bb); simpl; intros; try contradiction.
             assert (FR2: freshblock m2 m2' bb = true). eapply freshblockProp_char. split; trivial.
             rewrite FR2; simpl; trivial.
      - extensionality bb. rewrite <- (freshblock_trans m2 m2' m2''), orb_assoc; trivial.
    + f_equal.
      - extensionality bb. extensionality z.
        case_eq (L3 bb); simpl; intros.
        * repeat rewrite andb_false_r; simpl; trivial.
        * rewrite andb_true_r.
          case_eq (valid_block_dec m3 bb); simpl; intros.
          ++ rewrite andb_true_r, orb_assoc.
             case_eq (valid_block_dec m3' bb); simpl; intros.
             2: elim n; apply FWD3; trivial.
             assert (FR3: freshblock m3 m3' bb = false). apply freshblock_charF; left; trivial.
             rewrite FR3; simpl. trivial.
          ++ case_eq (U3' bb z); simpl; intros. 2: rewrite andb_false_r; trivial.
             assert (Mem.valid_block m3' bb). 
             { destruct StepN3 as [[nn StepNN] | [[nn StepNN] _]]; eapply effstepN_valid.
               apply StepNN. eassumption. apply StepNN. eassumption. }
             case_eq (valid_block_dec m3' bb); simpl; intros; try contradiction.
             assert (FR3: freshblock m3 m3' bb = true). eapply freshblockProp_char. split; trivial.
             rewrite FR3; simpl; trivial.
      - extensionality bb. rewrite <- (freshblock_trans m3 m3' m3''), orb_assoc; trivial.
  }
+ 
  (*case 2*)
   inv CS2. simpl in *. exists st3. exists m3.
   exists (d12',Some st2',d23).
   exists  (compose_meminj j12' j23), (fun b z => false). 
   split. { right. split. exists O. simpl; auto.
            apply t_step. constructor 1; auto. }
   destruct E3 as [M3 L3]. 
   split. { destruct INC12 as [INC12a INC12b].
            split. eapply compose_meminj_inject_incr. eassumption. apply inject_incr_refl.
            intros b1 b3 d JJ JJ'. 
            destruct (compose_meminjD_Some _ _ _ _ _ JJ') as [b2 [d1 [d2 [J12' [J23 D]]]]]. subst d; clear JJ'.
            destruct (compose_meminjD_None _ _ _ JJ).
            - destruct (INC12b _ _ _ H J12'). split; trivial.
              rewrite freshblock_irrefl in *.
              rewrite (match_wd23 _ _ _ _ _ _ _ _ _ _ MC23 _ _ _ J23) in *; trivial.
            - destruct H as [? [? [? ?]]]. 
              rewrite (INC12a _ _ _ H) in J12'; inv J12'. congruence. }
   split. { intros b1 b3 d J J'. 
            destruct (compose_meminjD_Some _ _ _ _ _ J') as [b2 [d1 [d2 [J12' [J23 D]]]]]. subst d; clear J'.
            destruct (compose_meminjD_None _ _ _ J); clear J.
            - destruct (Gsep12 _ _ _ H J12'); split; trivial. 
              admit. (*complete when right genv conditins are added apply (senv.equiv? _ _ g2 g3); try assumption.*)
            - destruct H as [? [? [? ?]]]. destruct INC12  as [INC12a _].
              rewrite (INC12a _ _ _ H) in J12'. inv J12'. congruence. } 
   { clear effcore_diagram23.
     exists st2'. exists m2'. exists j12', j23; eexists. (* repeat split; eauto.*)
     split; trivial. split; trivial. split. eassumption. simpl.
     exploit match_valid23. apply MC23. intros MV.
     split.
     + exact_eq MC23. f_equal.
       - f_equal.
         * extensionality b. extensionality z. rewrite orb_false_r.
           destruct MV as [MVa [MVb [MVc [MVd MVe]]]].
           case_eq (M2 b z); simpl; intros.
           -- destruct (MVd _ _ H) as [X Y]; rewrite Y; simpl.
             destruct (valid_block_dec m2' b); trivial. contradiction.
           -- rewrite andb_false_r; trivial.
         * extensionality b. rewrite freshblock_irrefl', orb_false_r; trivial. 
       - f_equal; extensionality b.
         -- extensionality z. rewrite orb_false_r.
            destruct MV as [MVa [MVb [MVc [MVd MVe]]]].
            case_eq (M3 b z); simpl; intros.
            ++ destruct (MVe _ _ H) as [X Y]; rewrite Y; simpl.
               destruct (valid_block_dec m3 b); trivial. contradiction.
            ++ rewrite andb_false_r; trivial.
         -- rewrite freshblock_irrefl, orb_false_r; trivial.
     + red; intros.
       destruct (match_wd12 _ _ _ _ _ _ _ _ _ _ MATCH12' _ _ _ H0). split. trivial. 
       destruct INC12 as [INC12a INC12b].
       case_eq (j12 b1); simpl; intros.
       - destruct p. rewrite (INC12a _ _ _ H1) in H0; inv H0. 
         apply orb_false_iff in H; destruct H.
         eapply (full _ _ _ H H1).
       - destruct (INC12b _ _ _ H1 H0). congruence. }
Admitted. (*OK, apart from the two admits on genv.*)

End CoreDiagrams_trans.