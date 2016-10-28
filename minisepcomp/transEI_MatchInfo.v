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

Require Import sepcomp.effect_semantics.

Require Import msl.Axioms. (*for extensionality*)

Require Import minisepcomp.mini_simulations_MatchInfo.
Require Import minisepcomp.mini_simulations_lemmas_MatchInfo.
Require Import Wellfounded.
Require Import Relations.
Require Import minisepcomp.mini_diagram_trans_MatchInfo. (*for compose_ord_eq_eq*)
Require Import minisepcomp.mem_interpolation_EI_MatchInfo.

Require Import minisepcomp.BuiltinEffects.

Import Mini_simulation_inj.

Import Mini_simulation_ext.

Lemma EffectsPropagate_EI j M1 M3 M2
      (EProp2 : EffectsPropagateE M1 M2)
      (EProp3 : EffectsPropagate j M2 M3):
  EffectsPropagate j M1 M3.
Proof. red; intros.  red in EProp2. red in EProp3.
    assert (X: forall b2 z, M2 b2 z = true -> j b2 <> None) by eauto.
    destruct (EProp3 X _ _ Ub) as [b1 [d [J Hb1]]].
    exists b1, d; split; trivial. eauto.
Qed.

(*
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
Proof. *)

Section EI_sim_trans.
Context {F1 V1 C1 F2 V2 C2 F3 V3 C3:Type}
        (Sem1 : @EffectSem (Genv.t F1 V1) C1)
        (Sem2 : @EffectSem (Genv.t F2 V2) C2)
        (Sem3 : @EffectSem (Genv.t F3 V3) C3)
        (g1 : Genv.t F1 V1)
        (g2 : Genv.t F2 V2)
        (g3 : Genv.t F3 V3).

Theorem EI_sim_trans: forall 
        (SIM12: @Mini_simulation_extend _ _ _ _ _ _ Sem1 Sem2 g1 g2)
        (SIM23: @Mini_simulation_inject _ _ _ _ _ _ Sem2 Sem3 g2 g3),
        @Mini_simulation_inject _ _ _ _ _ _ Sem1 Sem3 g1 g3.
Proof. 
  intros.
  destruct SIM12
    as [core_data12 match_core12 core_ord12 core_ord_wf12 
      senvs_dom_eq12 match_wd12 match_valid12 match_genv12
      core_initial12 effcore_diagram12
      core_halted12 core_at_external12 eff_after_external12]. 
  destruct SIM23 
    as [core_data23 match_core23 core_ord23 core_ord_wf23 
      match_wd23 senvs_dom_eq23 match_genv23
      match_valid23 core_initial23 effcore_diagram23
      core_halted23 core_at_external23 eff_after_external23].
  eapply Build_Mini_simulation_inject with
    (core_ord := clos_trans _ (sem_compose_ord_eq_eq core_ord12 core_ord23 C2))
    (match_state := fun d j E1 c1 m1 E3 c3 m3 => 
      match d with (d1,X,d2) => 
        exists c2, exists m2, exists M2,
          X=Some c2 /\ 
          match E1 with (M1, L1) =>
          match_core12 d1 c1 m1 (M1,L1,M2) c2 m2 /\ match_core23 d2 j (M2,L1) c2 m2 E3 c3 m3
          end
      end).
{ (*well_founded*)
  eapply wf_clos_trans. 
  eapply well_founded_sem_compose_ord_eq_eq; assumption. }
{ (*match_wd*) clear - match_wd12 match_wd23.
  intros. rename c2 into c3. rename m2 into m3. rename L2 into L3. rename b2 into b3.
  destruct d as [[d12 cc2] d23]. rename M2 into M3.
  destruct MS as [c2 [m2 [M2 [X [MC12 MC23]]]]]; subst.
  eapply (match_wd23 _ _ _ _ _ _ _ _ _ _ MC23); eassumption. }
{ (*senvs_domain_eq*)
  clear - senvs_dom_eq12 senvs_dom_eq23. destruct senvs_dom_eq12. 
   eapply senv_equiv_trans; eauto. }
(*{ (* ginfos_preserved  *)
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
  clear - match_genv23 match_genv12 match_valid23 match_valid12.
  intros. rename c2 into c3. rename m2 into m3. destruct E2 as [M3 L3]. 
  destruct d as [[d12 cc2] d23]. destruct E1 as [M1 L1].
  destruct MC as [c2 [m2 [M2 [X [MC12 MC23 ]]]]]; subst.
  destruct (match_genv12 _ _ _ _ _ _ _ _ MC12) as [GE12a [GE12b GE12c]].
  destruct (match_genv23 _ _ _ _ _ _ _ _ MC23) as [GE23a [GE23b GE23c]].
  assert (EQ: compose_meminj (Mem.flat_inj (Mem.nextblock m1)) j = j).
    { extensionality b. unfold compose_meminj.
      remember (Mem.flat_inj (Mem.nextblock m1) b) as q.
      destruct q.
      + destruct p. symmetry in Heqq. apply flatinj_E in Heqq.
        destruct Heqq as [? [? ?]]; subst. simpl.
        remember (j b) as w; destruct w; trivial. destruct p; trivial.
      + remember (j b) as w. destruct w; trivial. symmetry in Heqw; destruct p.
        destruct (match_valid23 _ _ _ _ _ _ _ _ MC23) as [MV23a [MV23b [MV23c [MV23d MV23e]]]].
        destruct (MV23c _ _ _ Heqw).
        eapply match_valid12 in H; try eassumption.
        erewrite flatinj_I in Heqq; try discriminate. apply H. }
  split; [| split].
  + exploit (symbols_inject_trans g1 g2 g3); eauto.
    rewrite EQ; trivial. 
  + rewrite <- EQ. apply meminj_preserves_genv2blocks.
         apply meminj_preserves_genv2blocks in GE12b.
         apply meminj_preserves_genv2blocks in GE23b.
         eapply meminj_preserves_globals_ind_compose. admit. (*apply genvs_dom_eq12.*)
         eassumption. eassumption.    
  + intros. eapply match_genv23. eassumption.
    admit. (*maybe true even with elimglobals phase*) }

{ (*meminj_valid*)
    clear - match_valid12 match_valid23.
    intros. rename c2 into c3. rename m2 into m3. destruct E2 as [M3 L3]. 
    destruct d as [[d12 cc2] d23]. destruct E1 as [M1 L1].
    destruct MS as [c2 [m2 [M2 [X [MC12 MC23]]]]]; subst.
    specialize (match_valid12 _ _ _ _ _ _ _ _ MC12).
    specialize (match_valid23 _ _ _ _ _ _ _ _ MC23). red in match_valid23.
    destruct match_valid23 as [MV23a [MV23b [MV23c [MV23d MV23e]]]].
    destruct match_valid12 as [MV12a [MV12b MV12c]]. 
    repeat split; intros.
    - apply MV12a. apply MV23a; trivial.
    - apply MV23b; trivial.
    - apply MV12a. eapply MV23c; eassumption.
    - eapply MV23c; eassumption.
    - eapply MV12b; eauto.
    - eapply MV12b; eauto.
    - eapply MV23e; eauto.
    - eapply MV23e; eauto. }
{ (*initial_core *)
  clear eff_after_external23 eff_after_external12 core_at_external23 core_at_external12.
  clear core_halted23 core_halted12 effcore_diagram23 effcore_diagram12. 
  intros. rename m2 into m3. rename vals2 into vals3. 
  assert (MR2: mem_respects_readonly g2 m1). { admit. (*TODO: add readonly-preservation clause to sim_extends_def?*) }
   destruct (core_initial12 _ _ _ _ _ _ H (forall_lessdef_refl vals1) (Mem.extends_refl m1)) as [cd12 [c2 [Ini2 MC12]]]; trivial.
   { destruct H2 as [PGa [PGb PGc]].
     repeat split; intros.
     + specialize (PGa _ _ H2). apply flatinj_I. 
       eapply Mem.valid_block_inject_1; eassumption. 
     + specialize (PGb _ _ H2). apply flatinj_I.
       eapply Mem.valid_block_inject_1; eassumption. 
     + apply flatinj_E in H6. destruct H6; trivial. }
   { clear - H3 H0 senvs_dom_eq12.
      destruct senvs_dom_eq12 as [[A1 [A2 A3]] A4].
      split. apply A2.
      split; intros. rewrite A1. apply flatinj_E in H. 
        destruct H as [? [? VB]]; subst; split; trivial.
      split; intros. rewrite A1. exists b1. split; trivial.
        destruct H3 as  [B1 [B2 [B3 B4]]]. destruct (B3 _ _ H H1) as [? [J C]].
        apply flatinj_I. eapply Mem.valid_block_inject_1; eauto.
      apply flatinj_E in H; destruct H as [? [? ?]]; subst. apply A3. }
   destruct (core_initial23 _ _ _ _ _ _ _ Ini2 H0 H1) as [cd23 [c3 [Ini3 MC23]]]; trivial.
   { admit. (*clear match_valid23 match_genv23 match_wd23 match_core23 core_initial23 core_initial12 core_ord23 core_ord_wf23 core_data23.
     destruct (match_genv12 _ _ _ _ _ _ MC12) as [A1 [A2 A3]]; clear match_genv12.
     specialize (match_valid12 _ _ _ _ _ _ MC12).
     clear match_wd12 H Ini2.
     destruct H2 as [B1 [B2 B3]]. destruct senvs_dom_eq12 as [X1 [X2 X3]].
     destruct A1 as [AA1 [AA2 [AA3 AA4]]].
     destruct A2 as [BB1 [BB2 BB3]].
     repeat split; intros.
     +  unfold Genv.find_symbol in H.  red in A1. red in A2. apply X1 in H. specialize (find_symbol_isGlobal _ _ _ H3); intros.
       rewrite <- (reach.genvs_domain_eq_isGlobal _ _ genvs_dom_eq12) in H4.
       eapply reach.meminj_preserves_globals_isGlobalBlock; eassumption.
     + specialize (find_var_info_isGlobal _ _ _ H3); intros.
       rewrite <- (reach.genvs_domain_eq_isGlobal _ _ genvs_dom_eq12) in H4.
       eapply reach.meminj_preserves_globals_isGlobalBlock; eassumption.
     + destruct ginfos_pres12 as [AA BB].
       destruct (gvar_infos_eqD2 _ _ AA _ _ H3) as [gv1 [FVI1 _]].
       destruct H2 as [PGa [PGb PGc]]. apply (PGc _ _ _ _ FVI1 H4).*) }
   { admit. (* clear match_valid23 match_genv23 match_wd23 match_core23 core_initial23 core_initial12 core_ord23 core_ord_wf23 core_data23.
     destruct (match_genv12 _ _ _ _ _ _ MC12) as [A1 [A2 A3]]; clear match_genv12.
     specialize (match_valid12 _ _ _ _ _ _ MC12). specialize (match_wd12 _ _ _ _ _ _ MC12).
     destruct H3 as [B1 [B2 [B3 B4]]].
     destruct A1 as [A11 [A12 [A13 A14]]].
     split. intros. rewrite B1, A11; trivial.
     split. intros. destruct H2. rewrite A11 in *. destruct (B2 _ _ _ _ H3 H4); subst. rewrite B1, A11; trivial.*) } 
   exists (cd12, Some c2, cd23), c3. split. assumption.
   unfold EmptyInfo, EmptyInfoE in *. 
   exists c2, m1, (fun b z => false). split; trivial. split; trivial. }
{ (*core diagram*) clear - match_wd12 senvs_dom_eq12 effcore_diagram23 match_valid23 match_wd23 effcore_diagram12.
   intros. rename st2 into st3. rename m2 into m3. destruct E2 as [M3 L3].
   destruct cd as [[d12 cc2] d23]. destruct E1 as [M1 L1].
   destruct H0 as [c2 [m2 [M2 [X [MC12 MC23]]]]]; subst.
   eapply (ext_inj_diagram Sem1 Sem2 Sem3 g1 g2 g3); eassumption. }
{ (*halted*) 
  clear - core_halted12 core_halted23; intros. 
  rename c2 into c3. rename m2 into m3. rename M2 into M3. rename L2 into L3.
  destruct cd as [[cd12 X] cd23]. destruct H as [c2 [m2 [M2 [? [MC12 MC23]]]]]; subst.
  destruct (core_halted12 _ _ _ _ _ _ _ _ _ MC12 H0) as [v2 [LDef [DRO1 [RDO2 [Halted2 [EXT12 EProp2]]]]]].
  destruct (core_halted23 _ _ _ _ _ _ _ _ _ _ _ MC23 Halted2) as [v3 [INJ23 [RDO2' [RDO3 [Vinj [Halted3 EProp3]]]]]].
  exists v3; split.
    eapply Mem.extends_inject_compose; eassumption.
  split. trivial. 
  split. trivial.
  split. eapply val_lessdef_inject_compose; eassumption.
  split; trivial.
  eapply EffectsPropagate_EI; eassumption.
  }
{ (*at_external*)
  clear - core_at_external23 core_at_external12; intros.
  rename c2 into st3. rename m2 into m3. rename M2 into M3. rename L2 into L3. 
  destruct cd as [[cd12 X] cd23]. destruct H as [st2 [m2 [M2 [? [MC12 MC23]]]]]; subst.
  
  destruct (core_at_external12 _ _ _ _ _ _ _ _ _ _ _ MC12 H0) as [EXT12 [RDO1 [RDO2 [EProp2 [args2 [Vals12 AtExt2]]]]]].
  destruct (core_at_external23 _ _ _ _ _ _ _ _ _ _ _ _ _ MC23 AtExt2) as [INJ23 [RDO2' [RDO3 [EProp3 [args3 [Vals23 AtExt3]]]]]].
  split. eapply Mem.extends_inject_compose; eassumption.
  split. trivial.
  split. trivial.
  split. eapply EffectsPropagate_EI; eassumption.
  exists args3; split; trivial. eapply forall_val_lessdef_inject_compose; eassumption. }
{ (*after_external*) 
  clear - match_wd12 match_valid12 core_at_external12 
          eff_after_external12  
          match_wd23 match_valid23 core_at_external23 
          eff_after_external23 senvs_dom_eq23 match_genv12 match_genv23
          senvs_dom_eq12.
  intros. rename st2 into st3. rename m2 into m3. rename L2 into L3. 
          rename vals2 into vals3'. rename m2' into m3'.
          rename RDO2 into RDO3. rename ret2 into ret3. rename HasTy2 into HasTy3.
          rename M2 into M3.
  destruct cd as [[d12 cc2] d23].
  destruct MatchMu as [st2 [m2 [M2 [X [MC12 MC23]]]]].
  assert (WDmu12:= match_wd12 _ _ _ _ _ _ _ _ MC12).
  assert (WDmu23:= match_wd23 _ _ _ _ _ _ _ _ _ _ MC23).  
  destruct (core_at_external12 _ _ _ _ _ _ _ _ _ _ _ MC12 AtExtSrc) as [EXT12 [RespRd1 [RespRd2 [EProp2 [vals2 [Vals12 AtExt2]]]]]].
  destruct (core_at_external23 _ _ _ _ _ _ _ _ _ _ _ _ _ MC23 AtExt2) as [INJ23 [RespRd2' [RespRd3 [EProp3 [vals3 [Vals23 AtExt3]]]]]].
  rewrite AtExtTgt in AtExt3; inv AtExt3.
  clear core_at_external12 core_at_external23.
  specialize (eff_after_external12 _ _ _ _ _ _ _ _ _ _ _ _
        MC12 AtExtSrc AtExt2 Vals12). 
  specialize (eff_after_external23 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INJ23
        MC23 AtExt2 AtExtTgt Vals23).
  destruct (match_valid12 _ _ _ _ _ _ _ _ MC12) as [MV12a [MV12b MV12c]].
  assert (GSep23: globals_separate m2 g3 j j').
  { red; intros. clear eff_after_external23 eff_after_external12.
    destruct (GSep _ _ _ J J'). split; trivial. intros N; apply H; clear H.
    eapply MV12a; eauto. }
  assert (INTER: exists m2', (*mini_extern_incr j12 j12' L1 L2 /\ mini_extern_incr j23 j23' L2 L3 /\
                             meminj_valid j12' L1 m1' L2 m2' /\ meminj_valid j23' L2 m2' L3 m3' /\*)
                             Mem.extends m1' m2' /\ mem_forward m2 m2' /\ Mem.inject j' m2' m3' /\
                             RDOnly_fwd m2 m2' (ReadOnlyBlocks g2) /\
                             Mem.unchanged_on (BuiltinEffects.o_o_reach (Mem.flat_inj (Mem.nextblock m1)) L1 m1) m2 m2' /\
                             Mem.unchanged_on (fun b1 _ => L1 b1 = true /\ j b1 = None) m2 m2').
  { eapply (interp_EI _ _ g2 _ _ g3 m1 m2 m1' m3 m3' j j' L1 L3 (ReadOnlyBlocks g1) (ReadOnlyBlocks g2) (ReadOnlyBlocks g3)); try eassumption.
    admit. (*RDO*) admit. (*RDO*) admit. (*RDO*) admit. (*RDO*) }

  destruct INTER as [m2' [EXT12' [Fwd2 [INJ23' [RDO2 [Unch2a Unch2b]]]]]].

  destruct (eff_after_external12 _ _ _ _ HasTy1 HasTy1 EXT12' (Val.lessdef_refl _) FwdSrc Fwd2 RDO1 RDO2 Unch2a)
    as [cd12 [st1' [st2'' [AftExt1 [AftExt2 MC12']]]]].
  assert (InjValid23': meminj_valid j' (M2,L1) (M3,L3) m2' m3').
  { destruct MV as [MVa [MVb [MVc [MVd MVe]]]].
    split; intros.
      apply (Mem.valid_block_extends _ _ _ EXT12'); apply (MVa _ H).
    split; intros.
      apply MVb; trivial.
    split; intros. destruct (MVc _ _ _ J).
      apply (Mem.valid_block_extends _ _ _ EXT12') in H. split; trivial.
    split; trivial.
    intros. destruct (MV12c _ _ H). split; trivial. apply Fwd2; trivial. } 

  assert (UnchTgt_OOR: Mem.unchanged_on (BuiltinEffects.o_o_reach j L3 m2) m3 m3').
  { split; intros.
    + apply UnchTgt.
    + apply UnchTgt; trivial. destruct H. split; trivial; intros.
      intros N. apply (H1 _ _ J). eapply Mem.perm_extends; eassumption.
    + apply UnchTgt; trivial. destruct H. split; trivial; intros.
      intros N. apply (H1 _ _ J). eapply Mem.perm_extends; eassumption. }

  destruct (eff_after_external23 j' _ _ _ _ HasTy1 HasTy3 INC GSep23 InjValid23' INJ23' RValInjNu' Fwd2 FwdTgt RDO2 RDO3 Unch2b UnchTgt_OOR)
    as [cd23 [st2' [st3' [AftExt2' [AftExt3 MC23']]]]].

  rewrite AftExt2 in AftExt2'. inv AftExt2'.

  exists ((cd12, Some st2'), cd23), st1', st3'.
  split. assumption.
  split. assumption.
  exists st2', m2', M2. split; trivial. split; trivial. }
Admitted. (*remaining admits are about readonly or at global blocks*)  

End EI_sim_trans. 