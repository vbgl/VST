Require Import compcert.common.Events. (*needed for standard definitions of 
                        mem_unchanged_on,loc_out-of_bounds etc etc*)
Require Import compcert.common.Memory.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import compcert.common.Values.
Require Import compcert.lib.Maps.
Require Import msl.Axioms.

Require Import sepcomp.mem_lemmas.
Require Import minisepcomp.mini_simulations.
Require Import minisepcomp.mem_interpolation_defs.

(*MATERIAL FROM compcomp/mem_interpolation_II.v*)
Require Import minisepcomp.mini_simulations_lemmas.

Require Import minisepcomp.FiniteMaps. (*Supersedes sepcomp/FiniteMaps.v ?*)

(***************************
 * UNSTRUCTURED INJECTIONS *
 ***************************)

(*Shifts the image of an injection by n up
 * The new target memory should be (size) large than
 *)
Definition shiftT (j: meminj) (n:block):meminj :=
  fun b =>
    match j b with
        | Some (b2, d) => Some ((b2 + n)%positive, d)
        | None => None
    end.
Infix ">>":= shiftT (at level 80, right associativity).

(*Shifts the domain of an injection down by n
 * The new target memory should be (size) large than
 *)
Definition shiftS (j: meminj) (n:block):meminj :=
  fun b => match ( b ?= n)%positive with
               | Gt => j (b - n)%positive
               | _ => None
           end.
Infix "<<":= shiftS (at level 80, right associativity).

Lemma shiftS_Some: forall j sh b1 p,
                     (j << sh) b1 = Some p ->
                     (b1 > sh)%positive /\ j (b1 - sh)%positive = Some p.
  unfold shiftS. intros.
  destruct (b1 ?= sh)%positive eqn:ineq; inversion H.
  split; trivial.
Qed.

(* fID satisfies (fID .*. f) = f and it's pure *)  
Definition filter_id (j:meminj): meminj:=
  fun b =>
    match j b with
        | Some _ => Some (b, 0)
        | None => None
    end.

(* filter *)  
Definition filter (j:meminj) (screen: block -> bool): meminj:=
  fun b =>
    if screen b then
      match j b with
        | Some _ => Some (b, 0)
        | None => None
      end
    else None.

Definition pure_filter (filt j: meminj): meminj :=
  fun b => 
    match filt b, j b with
        None, Some p => Some p
      | _, _ => None
    end.
        
(* size is the size of the memory being mapped
 * The new target memory should be (size) large than 
 * the original memory.
 *)
Definition add_inj (j k: meminj): meminj := 
  fun b =>
    match j b with
      | Some p => Some p
      | None => k b
    end.

Infix "(+)":= add_inj (at level 90, right associativity).

(* New definition for mkInjection
 * Assumes the new middle memory is the addition of m1 and m2
 * So everything mapped by j * k, is mapped identically
 * And everything else, mapped only by l, passes through the 
 * extra memory space added in m2 (of size m1).
 *)




Definition mkInjections (sizeM2:block)(j k l: meminj) 
                     :  meminj * meminj := 
   (j (+) (filter_id l >> sizeM2),
    k (+) ( pure_filter j l << sizeM2)).

(* Legacy: mkInjection that matches the type of the old version *)
Definition mkInjections' (m1 m1' m2 :mem)(j k l: meminj) 
                     :  meminj * meminj * block * block := 
  let n1 := Mem.nextblock m1' in
  let n2 := Mem.nextblock m2 in
  match mkInjections n2 j k l with
      | (j', k') => (j', k', n1, (n2 + n1)%positive)
                      end.


(**************************
 * mkInjection Properties *
 **************************)

Lemma pos_be_pos: forall a b, (a + b ?= b = Gt)%positive.
  intros. apply Pos.gt_iff_add. exists a. apply Pos.add_comm.
Qed.

Lemma MKIcomposition:
  forall j k l sizeM2,
    full_comp j k ->
    inject_incr (compose_meminj j k) l ->
    (forall b p, k b = Some p -> (b < sizeM2)%positive) ->
    forall  j' k',
      mkInjections sizeM2 j k l = (j', k') ->
      l = compose_meminj j' k'.
  unfold mkInjections; intros j k l ? full incr valid j' k' mk. inversion mk.
  unfold add_inj, shiftT, shiftS, compose_meminj, filter_id.
  extensionality b.
  destruct (j b) eqn:jb. destruct p.
  destruct (k b0) eqn:kb. destruct p.
  + apply incr. unfold compose_meminj; rewrite jb; rewrite kb; trivial.
  + apply full in jb. destruct jb as [b2 [d' kb0]]. rewrite kb0 in kb; inversion kb.
  + destruct (l b) eqn:lb; trivial.
    destruct (k (b + sizeM2)%positive) eqn: ksmthng. 
    - apply valid in ksmthng.
      clear - ksmthng; contradict ksmthng. rewrite Pos.add_comm; apply Pos.lt_not_add_l.
    - rewrite (Pos.add_sub). rewrite pos_be_pos; destruct p; auto.
      unfold pure_filter; rewrite jb; rewrite lb; auto.
Qed.

Lemma  MKI_incr12:
  forall j k l sizeM2,
    forall j' k',
      (j', k') = mkInjections sizeM2 j k l ->
   inject_incr j j'.
  intros j k l sizeM2 j' k' MKI; inversion MKI.
  unfold inject_incr, add_inj, shiftT. intros b b' d H; rewrite H; auto.
Qed.

Lemma  MKI_incr23:
  forall j k l sizeM2,
    forall j' k',
      (j', k') = mkInjections sizeM2 j k l ->
   inject_incr k k'.
  intros j k l sizeM2 j' k' MKI; inversion MKI.
  unfold inject_incr, add_inj, shiftT. intros b b' d H; rewrite H; auto.
Qed.

Lemma MKI_norm:
  forall j k l sizeM2,
    full_comp j k ->
    (forall b p, k b = Some p -> (b < sizeM2)%positive) ->
    forall j' k',
      (j', k') = mkInjections sizeM2 j k l ->
      full_comp j' k'.
  unfold full_comp. intros j k l sizeM2 full valid j' k' MKI b0 b1 delta1 mapj.
  inversion MKI.
  assert (map:= mapj); clear mapj.
  rewrite H0 in map; unfold add_inj in map.
  destruct (j b0) eqn:jb0.
  + destruct p; inversion map.
    apply full in jb0; destruct jb0 as [b2 [delta2 kb1]].
    exists b2, delta2.
    unfold add_inj, shiftT.
    subst b; rewrite kb1; auto.
  + unfold shiftT in map.
    destruct (filter_id l b0) eqn:filter_l; try solve[inversion map].
    destruct p; inversion map.
    unfold add_inj, shiftS.
    destruct (k (b + sizeM2)%positive) eqn:mapk.
    - apply valid in mapk.
      contradict mapk. rewrite Pos.add_comm; apply Pos.lt_not_add_l.
    - unfold filter_id in filter_l. destruct (l b0) eqn:lb0; try solve [inversion filter_l].
      destruct p. rewrite Pos.add_sub. inversion filter_l. subst b0.
      rewrite pos_be_pos; exists b2, z0.
      unfold pure_filter; rewrite jb0, lb0; trivial.
Qed.

Definition range_eq (j f:meminj) (sizeM:block):=
  forall b2 b1 delta, (b2 < sizeM)%positive -> f b1 = Some (b2, delta) -> j b1 = Some(b2, delta).

Lemma MKI_range_eq:
  forall j k l sizeM2,
  forall j' k',
    (j', k') = mkInjections sizeM2 j k l ->
    range_eq j j' sizeM2.
  intros j k l sizeM2 j' k' MKI; inversion MKI.
  unfold range_eq; intros b2 b1 delta range jmap'.
  unfold add_inj, shiftT in jmap'.
  destruct (j b1) eqn:jmap; trivial.
  destruct (filter_id l b1) eqn:lmap; trivial.
  destruct p; inversion jmap'.
  rewrite <- H2 in range.
  xomega.
Qed.

Lemma MKI_restrict:
  forall j k l sizeM2,
  forall j' k',
    (j', k') = mkInjections sizeM2 j k l ->
    forall b1 b2 delta, j' b1 = Some (b2, delta) ->
                        (b2 < sizeM2)%positive ->
                        j b1 = Some (b2, delta).
  intros. inversion H. unfold add_inj, shiftT in *; subst j'.
  destruct (j b1) eqn: jmap; trivial.
  destruct (filter_id l b1); trivial; destruct p.
  inversion H0. rewrite <- H3 in H1; xomega.
Qed.

Lemma MKI_no_overlap12:
  forall j k l sizeM2,
  forall j' k',
    (j', k') = mkInjections sizeM2 j k l ->
    forall m1 m1',
      Mem.meminj_no_overlap j m1 ->
      Mem.meminj_no_overlap l m1' ->
      mem_forward m1 m1' ->
      (forall b1 b2 d, j b1 = Some (b2, d) -> Mem.valid_block m1 b1) ->
      (forall b1 b2 d, j b1 = Some (b2, d) -> Plt b2 sizeM2) ->
      Mem.meminj_no_overlap j' m1'.
  unfold Mem.meminj_no_overlap; intros.
  inversion H. subst j'.
  Lemma add_inj_Some: forall j k b1 b2 d,
                        (j (+) k) b1 = Some (b2, d) ->
                        j b1 = Some (b2, d) \/
                        k b1 = Some (b2, d).
    unfold add_inj; intros. destruct (j b1).
    + destruct p; left; auto.
    + right; auto.
  Qed.
  apply add_inj_Some in H6; destruct H6 as [jmap1 | lmap1];
  apply add_inj_Some in H7; destruct H7 as [jmap2 | lmap2].
  (*1: Good case*)
  + eapply H0; eauto.
  - assert (Mem.valid_block m1 b1) by (eapply H3; eauto).
    eapply H2 in H6. destruct H6 as [Memval mperm].
    apply mperm; auto.
  - assert (Mem.valid_block m1 b2) by (eapply H3; eauto).
    eapply H2 in H6. destruct H6 as [Memval mperm].
    apply mperm; auto.
    (*2: Bad case/ contradiction*)
    + apply H4 in jmap1.
      unfold shiftT in lmap2. destruct ( filter_id l b2); try solve[inversion lmap2].
      destruct p. inversion lmap2.
      left. unfold not; intros.
      subst b1'. contradict jmap1. xomega.
    (*3: Bad case/ contradiction*)
    + apply H4 in jmap2.
      unfold shiftT in lmap1. destruct ( filter_id l b1); try solve[inversion lmap1].
      destruct p. inversion lmap1.
      left. unfold not; intros.
      subst b2'. contradict jmap2. xomega.
    (*4: Good case/ lmap*)
    + unfold shiftT in *.
      unfold filter_id in *.
      destruct (l b1) eqn:lmap1'; try solve [inversion lmap1]. destruct p.
      destruct (l b2) eqn:lmap2'; try solve [inversion lmap2]. destruct p.
      destruct (H1 _ _ _ _ _ _ _ _ H5 lmap1' lmap2' H8 H9) as [ineq1 | ineq2].
  - inversion lmap1; inversion lmap2. subst.
    left; clear - H5. unfold not; intros. 
    apply H5. eapply Pos.add_reg_r; eauto.
  - inversion lmap1; inversion lmap2. subst.
    left; clear - H5. unfold not; intros. 
    apply H5. eapply Pos.add_reg_r; eauto.
Qed.

Lemma MKI_None12:
  forall j k l sizeM2,
  forall j' k',
    (j', k') = mkInjections sizeM2 j k l ->
    forall b,
      j b = None ->
      l b = None ->
      j' b = None.
  intros ? ? ? ? ? ? H ? ? ? ; inversion H; 
  unfold add_inj, shiftT, filter_id, shiftS in *.
  subst; rewrite H0, H1; auto. 
Qed.

Lemma MKI_None23:
  forall j k l sizeM2,
  forall j' k',
    (j', k') = mkInjections sizeM2 j k l ->
    forall b,
      k b = None ->
      l (b - sizeM2)%positive = None ->
      k' b = None.
  intros ? ? ? ? ? ? H ? ? ? ; inversion H; 
  unfold add_inj, shiftT, filter_id, shiftS in *.
  unfold pure_filter; rewrite H0, H1; 
  destruct (b ?= sizeM2)%positive; destruct (j (b - sizeM2)%positive); trivial.
Qed.

Lemma MKI_Some12:
  forall j k l sizeM2,
  forall j' k',
    (j', k') = mkInjections sizeM2 j k l ->
    forall b b2 d,
      j' b = Some (b2, d) ->
      j b = Some (b2, d) \/ j b = None /\ (exists b2' d', l b = Some (b2', d') /\ b2 = (b + sizeM2)%positive /\ d = 0).
  intros. inversion H; clear H. 
  unfold add_inj, shiftT, filter_id, shiftS in *.
  subst.
  destruct (j b) eqn:jmap.
  destruct p; inversion H0; subst. left; auto.
  destruct (l b) eqn:lmap.
  destruct p; inversion H0; subst. right; split; trivial; exists b0, z; intuition.
  inversion H0.
Qed.

Lemma pure_filter_Some: forall filt j b1 p,
                          pure_filter filt j b1 = Some p ->
                          filt b1 = None /\ j b1 = Some p.
intros. unfold pure_filter in H. destruct (filt b1); inversion H.
destruct (j b1); inversion H1; auto.
Qed.

Lemma MKI_Some23:
  forall j k l sizeM2,
  forall j' k',
    (j', k') = mkInjections sizeM2 j k l ->
    forall b2 b3 d,
      k' b2 = Some (b3, d) ->
      k b2 = Some (b3, d) \/ k b2 = None /\ 
      (l (b2 - sizeM2)%positive = Some (b3, d) /\ 
       j (b2 - sizeM2)%positive = None /\
       (b2 ?= sizeM2)%positive = Gt).
  intros. inversion H; clear H. 
  unfold add_inj, shiftT, filter_id, shiftS in *.
  subst.
  destruct (k b2) eqn:jmap.
  destruct p; inversion H0; subst. left; auto.
  destruct ((b2 ?= sizeM2)%positive) eqn:ineq; try solve [inversion H0].
  right. apply pure_filter_Some in H0; destruct H0. auto. 
Qed.

Lemma MKI_Some12':
  forall j k l sizeM2,
    forall j' k',
      (j', k') = mkInjections sizeM2 j k l ->
      forall (b1 b2 : block) (d1 : Z),
        j' b1 = Some (b2, d1) ->
        j b1 = Some (b2, d1) \/
        (exists (b3 : block) (d : Z), l b1 = Some (b3, d)).
  intros.
  inversion H. subst j' k'.
  unfold add_inj, shiftT in H0.
  destruct (j b1) eqn:jb1.
  + left. destruct p; inversion H0; auto.
  + right. destruct (filter_id l b1) eqn:filtl; try solve [inversion H0].
    destruct p. unfold filter_id in filtl.
    destruct (l b1); try solve[ inversion filtl].
    destruct p as [b3 d]; exists b3, d; auto.
    
Qed.

Lemma MKI_Some23':
  forall j k l sizeM2,
    forall j' k',
      (j', k') = mkInjections sizeM2 j k l ->
      forall (b2 b3 : block) (d2 : Z),
        k' b2 = Some (b3, d2) ->
        k b2 = Some (b3, d2) \/
        (exists (b1 : block), l b1 = Some (b3, d2)).
  intros.
  inversion H. subst j' k'.
  unfold add_inj, shiftS in H0.
  destruct (k b2) eqn:jb2.
  + left. destruct p; inversion H0; auto.
  + right. destruct ((b2 ?= sizeM2)%positive); try solve[inversion H0].
    exists (b2 - sizeM2)%positive; trivial.
    apply pure_filter_Some in H0; destruct H0; auto.
Qed.

(*************************
 *         MEMORY        *
 *************************)
(*
Definition has_preimage (f:meminj) (m:mem) (b2:block):=
  exists b1 delta, Mem.valid_block m b1 /\ 
                   f b1 = Some (b2, delta).
Definition loc_preimage (f:meminj) (m:mem) (b2:block) (ofs:Z) :=
  exists b1 delta, Mem.valid_block m b1 /\ 
                   f b1 = Some (b2, delta) /\
                   Mem.perm m b1 (ofs - delta) Max Nonempty.

Definition acc_property (f:meminj) (m1' m2:mem)
           (AM:ZMap.t (Z -> perm_kind -> option permission)):Prop :=
  forall b2, 
    (Mem.valid_block m2 b2 -> 
     forall k ofs2,
       match source f m1' b2 ofs2 with
           Some(b1,ofs1) =>  (AM !! b2) ofs2 k = 
                             (m1'.(Mem.mem_access) !! b1) ofs1 k
         | None =>           (AM !! b2) ofs2 k = 
                             (m2.(Mem.mem_access) !! b2) ofs2 k
       end) /\
    (~ Mem.valid_block m2 b2 -> forall k ofs,
                             (AM !! b2) ofs k =
                             (m1'.(Mem.mem_access) !! (b2 - m2.(Mem.nextblock))%positive) ofs k).
*)

Definition mem_add_acc (j12 j23 j12' :meminj) (m1 m1' m2 : mem) (L2 B:block -> bool) :=
  fun b2 ofs2 k =>
       if valid_block_dec m2 b2 then 
         if B b2 then PMap.get b2 m2.(Mem.mem_access) ofs2 k else
           if L2 b2 then
               match source j12 m1 b2 ofs2 with
                   Some(b1,ofs1) => PMap.get b1 m1'.(Mem.mem_access) ofs1 k
                 | None =>  PMap.get b2 m2.(Mem.mem_access) ofs2 k
               end
           else match source j12 m1 b2 ofs2 with
                    Some(b1,ofs1) =>  PMap.get b1 m1'.(Mem.mem_access) ofs1 k
                  | None => match j23 b2 with 
                                None => PMap.get b2 m2.(Mem.mem_access) ofs2 k
                              | Some (b3,d3) =>  None 
                            end
                end
       else match source j12' m1' b2 ofs2 with 
                  Some(b1,ofs1) => PMap.get b1 m1'.(Mem.mem_access) ofs1 k
                | None =>  None
              end.
(*
Definition mem_add_acc j12 j23 (j12' :meminj) (m1 m1' m2 : mem) (B:block -> bool) :=
  fun b2 ofs2 k =>
       if valid_block_dec m2 b2 then 
         if B b2 then PMap.get b2 m2.(Mem.mem_access) ofs2 k else
           if (locBlocksSrc j23 b2) then
             if (pubBlocksSrc j23 b2) then
               match source (local_of j12) m1 b2 ofs2 with
                   Some(b1,ofs1) => if pubBlocksSrc j12 b1 
                                    then PMap.get b1 m1'.(Mem.mem_access) ofs1 k
                                    else PMap.get b2 m2.(Mem.mem_access) ofs2 k
                 | None =>  PMap.get b2 m2.(Mem.mem_access) ofs2 k
               end
             else PMap.get b2 m2.(Mem.mem_access) ofs2 k
           else match source (as_inj j12) m1 b2 ofs2 with
                    Some(b1,ofs1) =>  PMap.get b1 m1'.(Mem.mem_access) ofs1 k
                  | None => match (as_inj j23) b2 with 
                                None => PMap.get b2 m2.(Mem.mem_access) ofs2 k
                              | Some (b3,d3) =>  None (* This shouldn't happen by full_comp *)
                            end
                end
       else match source j12' m1' b2 ofs2 with 
                  Some(b1,ofs1) => PMap.get b1 m1'.(Mem.mem_access) ofs1 k
                | None =>  None
              end.

Definition mem_add_acc' j12 j23 (j12' :meminj) (m1 m1' m2 : mem) (B:block -> bool) :=
  fun b2 ofs2 =>
       if valid_block_dec m2 b2 then 
(*         if Mem.perm_dec m2 b2 ofs2 Max Writable then*)
         if B b2 then PMap.get b2 m2.(Mem.mem_access) ofs2 else
           if (locBlocksSrc j23 b2) then
             if (pubBlocksSrc j23 b2) then
               match source (local_of j12) m1 b2 ofs2 with
                   Some(b1,ofs1) => if pubBlocksSrc j12 b1 
                                    then fun k =>PMap.get b1 m1'.(Mem.mem_access) ofs1 k
                                    else fun k =>PMap.get b2 m2.(Mem.mem_access) ofs2 k
                 | None =>  fun k =>PMap.get b2 m2.(Mem.mem_access) ofs2 k
               end
             else fun k =>PMap.get b2 m2.(Mem.mem_access) ofs2 k
           else match source (as_inj j12) m1 b2 ofs2 with
                    Some(b1,ofs1) =>  fun k =>PMap.get b1 m1'.(Mem.mem_access) ofs1 k
                  | None => match (as_inj j23) b2 with 
                                None => fun k =>PMap.get b2 m2.(Mem.mem_access) ofs2 k
                              | Some (b3,d3) =>  fun k =>None 
                            end
                end
(*         else PMap.get b2 m2.(Mem.mem_access) ofs2*)
       else match source j12' m1' b2 ofs2 with 
                  Some(b1,ofs1) => fun k =>PMap.get b1 m1'.(Mem.mem_access) ofs1 k
                | None =>  fun k => None
              end.
*)
Definition mem_add_acc' (j12 j23 j12' :meminj) (m1 m1' m2 : mem) (L2 B:block -> bool) :=
  fun b2 ofs2 =>
       if valid_block_dec m2 b2 then 
         if B b2 then fun k => PMap.get b2 m2.(Mem.mem_access) ofs2 k else
           if L2 b2 then
               match source j12 m1 b2 ofs2 with
                   Some(b1,ofs1) => fun k => PMap.get b1 m1'.(Mem.mem_access) ofs1 k
                 | None =>  fun k => PMap.get b2 m2.(Mem.mem_access) ofs2 k
               end
           else match source j12 m1 b2 ofs2 with
                    Some(b1,ofs1) => fun k => PMap.get b1 m1'.(Mem.mem_access) ofs1 k
                  | None => match j23 b2 with 
                                None => fun k => PMap.get b2 m2.(Mem.mem_access) ofs2 k
                              | Some (b3,d3) => fun k => None 
                            end
                end
       else match source j12' m1' b2 ofs2 with 
                  Some(b1,ofs1) => fun k => PMap.get b1 m1'.(Mem.mem_access) ofs1 k
                | None => fun k => None
              end.

Lemma mem_add_acc_equiv: mem_add_acc = mem_add_acc'.
  extensionality j12;
  extensionality j23;
  extensionality j12';
  extensionality m1;
  extensionality m1';
  extensionality m2;
  extensionality L2;
  extensionality B;
  extensionality b2;
  extensionality of2;
  extensionality k.
  unfold mem_add_acc', mem_add_acc.
  destruct (valid_block_dec m2 b2).
(*  destruct (Mem.perm_dec m2 b2 of2 Max Writable); trivial. rename p into PWR.*)
+ destruct (B b2); trivial.
  destruct (L2 b2); trivial.  
  destruct (source j12 m1 b2 of2); trivial.
  destruct p as [b1 ofs1]; trivial.
  destruct (source j12 m1 b2 of2).
  destruct p; trivial.
  destruct (j23 b2); trivial. 
  destruct p; trivial.
+ destruct (source j12' m1' b2 of2); trivial.
  destruct p; trivial.
Qed.

Lemma mem_add_acc_cases: 
  forall j12 j23 (j12' :meminj) (m1 m1' m2 : mem) L2 B,
    forall b ofs,
      (mem_add_acc j12 j23 j12' m1 m1' m2 L2 B b ofs = PMap.get b m2.(Mem.mem_access) ofs) \/
      (mem_add_acc j12 j23 j12' m1 m1' m2 L2 B b ofs = fun _ => None) \/
      (exists b1 ofs1,
         mem_add_acc j12 j23 j12' m1 m1' m2 L2 B b ofs = PMap.get b1 m1'.(Mem.mem_access) ofs1).
Proof. intros. rewrite mem_add_acc_equiv; unfold mem_add_acc'.
  remember (mem_add_acc' j12 j23 j12' m1 m1' m2 L2 B b ofs) as f.
  unfold mem_add_acc' in Heqf.
  destruct (valid_block_dec m2 b).
+ destruct (B b). left; trivial.
  destruct (L2 b).
  - destruct (source j12 m1 b ofs).
    destruct p as [b1 ofs1]. right; right. exists b1, ofs1; extensionality k; auto. 
    left. extensionality k; auto.
  - destruct (source j12 m1 b ofs).
    * destruct p as [b1 ofs1]. right; right. exists b1, ofs1; extensionality k; auto.
    * destruct (j23 b).
      destruct p. right; left; trivial.
      left; trivial.
+ destruct (source j12' m1' b ofs).
  destruct p as [b1 ofs1]. right; right. exists b1, ofs1; extensionality k; auto. 
    right; left; trivial.
Qed.

(* Short section about injecting memvals*)
Definition inject_val (f:meminj) (v:val): option val :=
  match v with
(*    Vundef => None*)
  | Vptr b i => match f b with None => None 
                | Some (b', d) => Some (Vptr b' (Int.add i (Int.repr d)))
                end
  | _ => Some v
  end.

Lemma inject_val_val_inject: forall j v v' 
  (IM: inject_val j v = Some v'), val_inject j v v'.
Proof.
  intros.
  destruct v; destruct v'; simpl in *; try congruence; try inv IM; try constructor.
  + destruct (j b); inv H0. destruct p; congruence.
  + destruct (j b); inv H0. destruct p; congruence.
  + destruct (j b); inv H0. destruct p; congruence.
  + destruct (j b); inv H0. destruct p; congruence.
  + destruct (j b); inv H0. destruct p; congruence.
  + remember (j b) as d. destruct d; inv H0.
    destruct p; inv H1. econstructor. rewrite <- Heqd; trivial. trivial.
Qed.

Definition inject_memval (j:meminj) (v:memval): memval := 
     match v with 
         Fragment v q n =>
             match inject_val j v with 
                None => Undef
              | Some v' => Fragment v' q n 
             end
       | _ => v
     end.

Lemma inject_memval_memval_inject: forall j v v' 
  (IM: inject_memval j v = v') (U: v' <> Undef), memval_inject j v v'.
Proof.
  intros.
  destruct v; destruct v'; simpl in *; try congruence; try inv IM; try constructor.
  + destruct (inject_val j v); inv H0.
  + remember (inject_val j v) as d. destruct d; inv H0. constructor.
    apply inject_val_val_inject. rewrite Heqd; trivial. 
Qed.

Lemma inject_memval_memval_inject1 j v
      (H: forall u q n, v = Fragment u q n -> 
          exists p, inject_val j u = Some p):
      memval_inject j v (inject_memval j v). 
Proof.
  destruct v; simpl in *; try constructor.
  destruct (H _ _ _ (eq_refl _)) as [p P]; clear H. rewrite P.
  constructor. apply inject_val_val_inject; trivial. 
Qed.

(* End of inject_memval *)

Definition mem_add_nb (m1 m2:mem):=
  let n1 := Mem.nextblock m1 in
  let n2 := Mem.nextblock m2 in
  (n2 + n1)%positive. 


(* The first injection maps blocks and pointers, 
 * the second one defines what is mapped and what
 * is coppied from m2. 
Dead definition?
Definition mem_add_cont' (j k:meminj)(f:meminj) (m1' m2:mem):=
  fun b2 ofs2 =>
    if valid_block_dec m2 b2 then 
      (match source f m1' b2 ofs2 with
           Some(b1,ofs1) =>inject_memval j (ZMap.get ofs1 (PMap.get b1 m1'.(Mem.mem_contents)))
         | None =>      ZMap.get ofs2 ( m2.(Mem.mem_contents) !! b2)
       end)
    else inject_memval j (ZMap.get ofs2 (m1'.(Mem.mem_contents) !! (b2 - m2.(Mem.nextblock)))).
*)

Definition mem_add_cont (j12 j23 j12' :meminj) (m1 m1' m2 : mem) (L2 B:block -> bool) :=
fun b2 ofs2 =>
  if valid_block_dec m2 b2 then 
    if B b2 then ZMap.get ofs2 (m2.(Mem.mem_contents) !! b2) else
    if L2 b2 then
          match source j12 m1 b2 ofs2 with
            | Some(b1,ofs1) => match j23 b2 with 
                                   None => ZMap.get ofs2 ( m2.(Mem.mem_contents) !! b2)
                                 | Some _ => inject_memval j12' (ZMap.get ofs1 (PMap.get b1 m1'.(Mem.mem_contents)))
                               end
            | None =>  ZMap.get ofs2 ( m2.(Mem.mem_contents) !! b2)
          end
      else 
        match source j12 m1 b2 ofs2 with
          | Some(b1,ofs1) =>inject_memval j12' (ZMap.get ofs1 (PMap.get b1 m1'.(Mem.mem_contents)))
          | None => 
            match j23 b2 with 
                None =>  ZMap.get ofs2 ( m2.(Mem.mem_contents) !! b2)
              | Some (b3,d3) =>  Undef (* This shouldn't happen by full_comp *)
            end
        end
    (*else ZMap.get ofs2 ( m2.(Mem.mem_contents) !! b2)*)
  else
      match source j12' m1' b2 ofs2 with 
        | Some(b1,ofs1) => inject_memval j12' (ZMap.get ofs1 (PMap.get b1 m1'.(Mem.mem_contents)))
        | None =>  (*Undef*) ZMap.get ofs2 (fst (Mem.mem_contents m2))
      end.

Definition meminj_validblock_2 f m2 := forall (b b' : block) (delta : Z),
                               f b = Some (b', delta) -> Mem.valid_block m2 b'.

Definition meminj_validblock_2' f N2 := forall (b b' : block) (delta : Z),
                               f b = Some (b', delta) -> Plt b' N2.

Lemma finite_acc: forall j12 j23 j12' m1 m1' m2 L2 B
                    (VB2_j12: meminj_validblock_2 j12 m2)
                    (VB2_j12': meminj_validblock_2' j12' (mem_add_nb m1' m2))
                    (b : positive),
                    (b >= mem_add_nb m1' m2)%positive ->
                    mem_add_acc j12 j23 j12' m1 m1' m2 L2 B b = (fun _ _ => None).
Proof. intros.
  extensionality x; extensionality k; unfold mem_add_acc.
  assert (sour: source j12 m1 b x = None).
  { destruct (source j12 m1 b x) eqn:sour; trivial.
    symmetry in sour; apply source_SomeE in sour.
    destruct sour as 
        [b02 [delta' [ofs2 [invert [ineq [jmap [mperm ofseq]]]]]]].
    apply VB2_j12 in jmap. unfold Mem.valid_block, Plt in jmap.
    apply Pos.ge_le_iff in H. 
    unfold Pos.le in H; contradict H. apply Pos.gt_lt_iff.
    eapply Pos.lt_trans. exact jmap.
    unfold mem_add_nb. xomega. }

  assert (sour12': source j12' m1' b x = None).
  { destruct (source j12' m1' b x) eqn:sour12'; trivial.
    symmetry in sour12'; apply source_SomeE in sour12'.
    destruct sour12' as 
        [b02 [delta' [ofs2 [invert [ineq [jmap [mperm ofseq]]]]]]].
    apply VB2_j12' in jmap. unfold Mem.valid_block, Plt in jmap. 
    unfold Pos.ge in H; contradict H. apply jmap. }
  
  rewrite sour, sour12'.
  assert (HH: forall k, (Mem.mem_access m2) !! b x k = None).
  { intros. apply (Mem.nextblock_noaccess m2). 
    intro HH.
    apply Pos.ge_le_iff in H. 
    unfold Pos.le in H; contradict H. apply Pos.gt_lt_iff.
    eapply Pos.lt_trans. exact HH.
    unfold mem_add_nb. xomega. }
  rewrite HH.
  (*Do the cases*)
  destruct (valid_block_dec m2 b); trivial. 
  destruct (B b); trivial.
  destruct (L2 b); trivial.
  destruct (j23 b); trivial. destruct p; trivial.
Qed.

Lemma acc_construct :
  forall j12 j23 j12' m1 m1' m2 L2 B
         (VB2_j12: meminj_validblock_2 j12 m2)
         (VB2_j12': meminj_validblock_2' j12' (mem_add_nb m1' m2)),
  exists mem_access:PMap.t (Z -> perm_kind -> option permission),
    (forall b, mem_access !! b = mem_add_acc j12 j23 j12' m1 m1' m2 L2 B b) /\
    (forall (b : positive) (ofs : Z),  Mem.perm_order'' (mem_access !! b ofs Max)
                                                        (mem_access !! b ofs Cur)) /\
    (forall (b : positive) (ofs : Z) (k : perm_kind),
                         ~ Plt b (mem_add_nb m1' m2) -> mem_access !! b ofs k = None).
Proof. intros. 
  remember (finite_acc _ j23 _ m1 _ _ L2 B VB2_j12 VB2_j12') as finite_proof.
  destruct (pmap_construct _                                       (*A*)
                           (mem_add_acc j12 j23 j12' m1 m1' m2 L2 B)  (*f*)
                           (mem_add_nb m1' m2)                     (*hi*)
                           (fun _ _ => None)                       (*dfl*)
                           (finite_proof))                         (*proof*)
  as [mem_access property].
  exists mem_access; intuition.
  + rewrite property;
    destruct (mem_add_acc_cases j12 j23 j12' m1 m1' m2 L2 B b ofs) as 
        [caseM2 | [caseNone | [b1 [ofs1 caseM1']]]].
    - rewrite caseM2. apply m2.
    - rewrite caseNone; unfold Mem.perm_order''; trivial.
    - rewrite caseM1'; apply m1'.
  + rewrite property; rewrite finite_proof; trivial.
Qed.    


Require Import Zwf.

Lemma block_content_superbound: forall m,
                                  sigT (fun lo =>
                                          sigT (fun hi =>
                                    forall b ofs,
                                      (ofs<lo \/ ofs>hi)->
                                      ZMap.get ofs ( m.(Mem.mem_contents) !! b) = Undef)).
Proof. intros. destruct (pmap_finite_type _ (Mem.mem_contents m)) as [N property].
  destruct (zmap_finite_type _ (fst (Mem.mem_contents m))) as [lo0 [hi0 property0]].
  cut ( sigT (fun lo =>
                sigT (fun hi =>
                        forall b ofs,
                          (N > b)%positive ->
                          (ofs<lo \/ ofs>hi)->
                          ZMap.get ofs ( m.(Mem.mem_contents) !! b) = Undef) )) .
  { intros X. destruct X as [lo1 [hi1 property1]]. 
    exists (Z.min lo0 lo1); exists (Z.max hi0 hi1).
    intros. destruct (N ?= b)%positive eqn:Nb. 
    + rewrite property, property0.
      rewrite <- (property N). apply m. 
      - xomega. 
      - destruct H; xomega. 
      - intros HH. rewrite Nb in HH; inversion HH.
    + rewrite property, property0.
      rewrite <- (property N). apply m. 
      - xomega. 
      - destruct H; xomega. 
      - intros HH. rewrite Nb in HH; inversion HH.
    + apply property1; trivial. destruct H; xomega. }
  { generalize N. clear N property property0 lo0 hi0.
    specialize (well_founded_induction_type  (Plt_wf)). intros HH.
    apply (HH (fun N : positive =>
          {lo : Z &
          {hi : Z &
          forall (b : positive) (ofs : Z),
          (N > b)%positive ->
          ofs < lo \/ ofs > hi ->
          ZMap.get ofs (Mem.mem_contents m) !! b = Undef}})); intros.
    destruct (x ?= 1)%positive eqn:X.
    + apply Pos.compare_eq_iff in X.
      subst x. exists 1, 1; intros. contradict H0. xomega. 
    + contradict X. apply Pos.nlt_1_r.
    + (*Inductive step*)
      destruct (H (Pos.pred x)) as [lo0 [hi0 property0]]. apply Ppred_Plt. intros Xeq. 
      rewrite <- Pos.compare_eq_iff in Xeq. congruence.
      destruct (zmap_finite_type _ (Mem.mem_contents m) !! (Pos.pred x)) as [lo1 [hi1 property1]].
      exists (Z.min lo0 lo1), (Z.max hi0 hi1).
      intros. 
      destruct (Pos.pred x ?= b)%positive eqn:xb.
      - rewrite Pos.compare_eq_iff in xb; subst b.
        rewrite property1. apply m.
        destruct H1; xomega.
      - cut False; try contradiction ; clear - X xb H0. 
        apply Pos.succ_lt_mono in xb. 
        apply Pos.lt_succ_r in xb.
        rewrite Pos.succ_pred in xb. xomega.
        xomega.
      - apply property0. exact xb.
        destruct H1; xomega. }
Qed.

Definition mi_freeblocks (f: meminj) m := 
    forall b : block, ~ Mem.valid_block m b -> f b = None.

Lemma delta_superbound: forall (j:meminj) N,
                          sigT ( fun lod =>
                                   sigT (fun hid =>
                                    forall b,
                                      forall b' d, 
                                        (b < N)%positive ->
                                        j b = Some (b', d) ->
                                                   d < hid /\ d > lod)).
  intros j.
  specialize (well_founded_induction_type  (Plt_wf)). intros HH.
  apply (HH (fun N : positive =>
         {lod : Z &
         {hid : Z &
          forall (b : positive) (b' : block) (d : Z),
          (b < N)%positive -> j b = Some (b', d) -> d < hid /\ d > lod}})); intros.
  destruct (peq x 1).
  + exists 1, 1; intros. subst x. contradict H0; xomega.
  + destruct (H (x-1)%positive) as [lo [hi property]].
    { apply Ppred_Plt in n; xomega. }
    { destruct (j (x-1)%positive) eqn:jmap; try destruct p as [b' d].
      - exists (Z.min lo (d - 1)), (Z.max hi (d + 1)); intros.
        destruct (b ?= (x - 1))%positive eqn:bx.
        * apply Pos.compare_eq_iff in bx; subst b. 
          rewrite jmap in H1; inversion H1. xomega.
        * apply (property _ _ _ bx) in H1. xomega.
        * rewrite Pcompare_eq_Gt in bx. rewrite Pos.gt_lt_iff in bx.
          apply Pos.succ_lt_mono in bx. 
          apply Pos.lt_succ_r in bx.
          rewrite Pplus_one_succ_r, Pos.sub_add in bx; xomega.
      - exists lo, hi; intros.
        eapply property; eauto.
        destruct (b ?= (x - 1))%positive eqn:bx.
        * apply Pos.compare_eq_iff in bx; subst b. congruence.
        * trivial.
        * rewrite Pcompare_eq_Gt in bx. rewrite Pos.gt_lt_iff in bx.
          apply Pos.succ_lt_mono in bx. 
          apply Pos.lt_succ_r in bx.
          rewrite Pplus_one_succ_r, Pos.sub_add in bx; xomega. }
 Qed.
           
Lemma finite_cont_perblock: forall j12 j23 j12' m1 m1' m2 L2 B
                              (INCR: inject_incr j12 j12'),
                          forall b,
                   sigT ( fun lo => 
                            sigT (fun hi =>
                     forall z : Z, z < lo \/ z > hi -> 
                                   mem_add_cont j12 j23 j12' m1 m1' m2 L2 B b z = Undef)).
Proof. intros.
  destruct (block_content_superbound m1') as [lo1 [hi1 bound1]].
  destruct (delta_superbound  j12' (Pos.max (Mem.nextblock m1) (Mem.nextblock m1'))) 
    as [lod [hid boundd]].
  destruct (zmap_finite_type _ (Mem.mem_contents m2) !! b) as [lo2 [hi2 bound2]].
  destruct (zmap_finite_type _ (fst (Mem.mem_contents m2))) as [lo3 [hi3 bound3]].
  (*exists (Z.min (lo1 + lod) (Z.min lo2 lo3 )), (Z.max (hi1 + hid) (Z.max hi2 hi3)).*)
  exists (Z.min (lo1 + lod) (Z.min lo2 lo3 )), (Z.max (hi1 + hid) (Z.max hi2 hi3)).
  intros. unfold mem_add_cont.
  assert (HH: ZMap.get z (Mem.mem_contents m2) !! b = Undef).
  { erewrite bound2.
    apply m2. destruct H; xomega. }
  rewrite HH.
  (*Now do the cases *)
  destruct (valid_block_dec m2 b).
  + (*destruct (Mem.perm_dec m2 b z Max Writable); trivial.
    rename p into PWR.*)
    destruct (B b); trivial. 
    destruct (L2 b). 
    - destruct (source j12 m1 b z) eqn:sour12; trivial.
      destruct p.
      destruct (j23 b); trivial. 
      assert (ZMap.get z0 (Mem.mem_contents m1') !! b0 = Undef).
      { symmetry in sour12; apply source_SomeE in sour12.
        destruct sour12 as 
            [b02 [delta' [ofs2 [invert [ineq [jmap [mperm ofseq]]]]]]].
        inversion invert. subst.
        
        assert (jmap': j12' b02 = Some (b, delta')) by (apply INCR; trivial).
        apply boundd in jmap'; destruct jmap'.
        apply bound1. destruct H; [left | right]; xomega. 
        apply Pos.max_lt_iff; auto. }
      rewrite H0; auto. 
    - destruct (source j12 m1 b z) eqn: sour;
      try solve [ destruct (j23 b); try destruct p; trivial].
      destruct p.
      assert (ZMap.get z0 (Mem.mem_contents m1') !! b0 = Undef).
      { symmetry in sour; apply source_SomeE in sour.
        destruct sour as 
            [b02 [delta' [ofs2 [invert [ineq [jmap [mperm ofseq]]]]]]].
        inversion invert.
        assert (jmap': j12' b02 = Some (b, delta')) by (apply INCR; trivial).
        apply boundd in jmap'; auto; destruct jmap'.
        apply bound1. destruct H; [left | right]; xomega.
        apply Pos.max_lt_iff; auto. }
      rewrite H0; auto.
  + destruct (source j12' m1' b z) eqn:sour; trivial.
    - destruct p.
      assert (ZMap.get z0 (Mem.mem_contents m1') !! b0 = Undef).
      {  symmetry in sour; apply source_SomeE in sour.
         destruct sour as 
             [b02 [delta' [ofs2 [invert [ineq [jmap' [mperm ofseq]]]]]]].
         inversion invert.
         apply boundd in jmap'; auto; destruct jmap'.
         apply bound1. destruct H; [left | right]; xomega.
         apply Pos.max_lt_iff; auto. }
      rewrite H0; trivial.
    - destruct (pmap_finite _ (Mem.mem_contents m2)) as [N bound].
      rewrite bound3. 
      rewrite <- (bound N).
      apply m2. xomega.
      xomega.
Qed.

Lemma cont_construct_perblock: 
  forall j12 j23 j12' m1 m1' m2 L2 B (INCR: inject_incr j12 j12'),
  forall b,
  sigT (fun mem_contents_block: ZMap.t memval =>
    (forall ofs, ZMap.get ofs mem_contents_block = mem_add_cont j12 j23 j12' m1 m1' m2 L2 B b ofs) /\
    (fst mem_contents_block = Undef)) .
Proof. intros.
  destruct (finite_cont_perblock _ j23 j12' m1 m1' m2 L2 B INCR b) as [lo [hi finite_proof]].
  destruct (zmap_construct_type 
                           _                                         (*A*)
                           (mem_add_cont j12 j23 j12' m1 m1' m2 L2 B b) (*f*)
                           (lo)                                      (*lo*)
                           (hi)                                      (*hi*)
                           (Undef)                                   (*dfl*)
                           (finite_proof))                          (*proof*)
  as [mem_contents_block property].
  exists mem_contents_block; intuition.
  destruct (zmap_finite _ mem_contents_block) as [lo' [hi' bound]].
  rewrite <- (bound (Z.max (hi + 1) (hi' + 1)) ); try solve[xomega]. 
  rewrite property; apply finite_proof; xomega.
Qed.

Lemma finite_cont: forall j12 j23 j12' m1 m1' m2 L2 B
                    (VB2_j12: meminj_validblock_2 j12 m2)
                    (VB2_j12': meminj_validblock_2' j12' (mem_add_nb m1' m2)),
                   exists N,
                  forall n : positive,
                    (n >= Pmax (mem_add_nb m1' m2) N )%positive ->
                    mem_add_cont j12 j23 j12' m1 m1' m2 L2 B n = 
                    (fun z => ZMap.get z (fst (Mem.mem_contents m2))) .
Proof. intros.
  destruct (pmap_finite _ (Mem.mem_contents m2)) as [N bound]; exists N.
  intros.
  extensionality x; unfold mem_add_cont.
  assert (sour: source j12 m1 n x = None).
  { destruct (source j12 m1 n x) eqn:sour; trivial.
    symmetry in sour; apply source_SomeE in sour.
    destruct sour as 
        [b02 [delta' [ofs2 [invert [ineq [jmap [mperm ofseq]]]]]]].
   apply VB2_j12 in jmap. unfold Mem.valid_block, Plt in jmap. 
   apply Pos.ge_le_iff in H. apply Pos.max_lub_l in H.
   unfold Pos.le in H; contradict H. apply Pos.gt_lt_iff.
   eapply Pos.lt_trans. exact jmap.
   unfold mem_add_nb. xomega.
  }

  assert (sour12': source j12' m1' n x = None).
  { destruct (source j12' m1' n x) eqn:sour12'; trivial.
    symmetry in sour12'; apply source_SomeE in sour12'.
    destruct sour12' as 
        [b02 [delta' [ofs2 [invert [ineq [jmap [mperm ofseq]]]]]]].
   apply VB2_j12' in jmap. unfold Mem.valid_block, Plt in jmap. 

   apply Pos.ge_le_iff in H. apply Pos.max_lub_l in H.
   unfold Pos.le in H; contradict H. apply Pos.gt_lt_iff; trivial.
  }
  
  rewrite sour, sour12', bound.
  { destruct (valid_block_dec m2 n); trivial.
    (*destruct (Mem.perm_dec m2 n x Max Writable); trivial.
    rename p into PWR.*)
    destruct (B n); trivial.
    destruct (L2 n); trivial.
    destruct (j23 n) eqn:map23; trivial.
    destruct p. unfold Mem.valid_block, Plt in v.  
      apply Pos.ge_le_iff in H. apply Pos.max_lub_l in H.
      unfold Pos.le in H; contradict H. apply Pos.gt_lt_iff.
      eapply Pos.lt_trans. exact v.
      unfold mem_add_nb. xomega. }
  eapply Pos.max_lub_r. eapply Pos.ge_le_iff; exact H.
Qed.

Lemma try: forall A B (P: A -> B -> Prop),
             (forall b, sigT (fun M => P b M)) ->
             exists f, forall b, P b (f b).
Proof. intros. exists (fun b => projT1 (X b)).
  intros b; destruct (X b); auto.
Qed.

Lemma cont_construct_step1: 
  forall j12 j23 j12' m1 m1' m2 L2 B
         (VB2_j12: meminj_validblock_2 j12 m2)
         (VB2_j12': meminj_validblock_2' j12' (mem_add_nb m1' m2))
         (INCR: inject_incr j12 j12'),
  exists mem_contents: block -> (ZMap.t memval),
  (forall b ofs,
    (ZMap.get ofs (mem_contents b) = 
                 mem_add_cont j12 j23 j12' m1 m1' m2 L2 B b ofs) /\
    (fst (mem_contents b) = Undef))  .
Proof. intros.
  remember (fun b M => forall  (ofs : ZIndexed.t),
     ZMap.get ofs M =
     mem_add_cont j12 j23 j12' m1 m1' m2 L2 B b ofs /\
     fst M = Undef) as P.
  cut (exists f, forall b, (P b (f b))).
  { subst P; intros. destruct H. exists x. exact H. }
  { apply try. intros. 
  destruct (finite_cont_perblock _ j23 j12' m1 m1' m2 L2 B INCR b) as [hi [lo finite_block']].
  destruct (cont_construct_perblock j12 j23 j12' m1 m1' m2 L2 B INCR b) as 
      [block_content [cont_property dfl_property]].
  exists block_content.
  subst P. intros; split.
  rewrite cont_property; trivial.
  trivial. }
Qed.

Lemma cont_construct: 
  forall j12 j23 j12' m1 m1' m2 L2 B
         (VB2_j12: meminj_validblock_2 j12 m2)
         (VB2_j12': meminj_validblock_2' j12' (mem_add_nb m1' m2))
         (INCR: inject_incr j12 j12'),
  exists mem_contents: PMap.t (ZMap.t memval),
    (forall b ofs, ZMap.get ofs (mem_contents !! b) = 
                 mem_add_cont j12 j23 j12' m1 m1' m2 L2 B b ofs) /\
    (forall b, fst (mem_contents !! b) = Undef).
Proof. intros.
  destruct (cont_construct_step1 _ j23 _ m1 _ _ L2 B VB2_j12 VB2_j12' INCR) 
          as [mem_contents_f' prop].
  remember ( fst (Mem.mem_contents m2)) as dfl.
  destruct (finite_cont _ j23 _ m1 _ _ L2 B VB2_j12 VB2_j12') as [N finite_proof].
  remember (Pos.max (mem_add_nb m1' m2) N)%positive as hi.
  remember (fun n => match (n ?= hi)%positive with
                         | Eq | Gt => dfl
                         | Lt => mem_contents_f' n end ) as mem_contents_f.
  assert (finite: forall n : positive, (n >= hi)%positive -> mem_contents_f n = dfl).
  { intros; subst dfl.
    subst mem_contents_f. unfold Pos.ge in H. destruct (n ?= hi)%positive; trivial.
    contradict H; trivial. }
  destruct (pmap_construct _                                       (*A*)
                           (mem_contents_f)  (*f*)
                           (hi)                     (*hi*)
                           (dfl)  (*dfl*)
                           (finite))                         (*proof*)
  as [mem_access property].
  exists mem_access; intros.
  split; intros.
  + destruct (prop b ofs) as [map_func default].
    rewrite property.
    subst mem_contents_f; destruct (b ?= hi)%positive eqn:bhi; trivial;
    subst dfl; rewrite finite_proof; try split; auto;
    try solve [unfold Pos.ge; rewrite bhi; intros HH; inversion HH].
  + destruct (prop b Z0) as [map_func default].
    rewrite property; subst mem_contents_f; 
    destruct (b ?= hi)%positive eqn:bhi; trivial; subst dfl.
  { destruct (pmap_finite _ ((Mem.mem_contents m2))) as [N' stuff].
   rewrite <- (stuff (N' + 1)%positive). apply m2. xomega. }
  { destruct (pmap_finite _ ((Mem.mem_contents m2))) as [N' stuff].
   rewrite <- (stuff (N' + 1)%positive). apply m2. xomega. }
Qed.

Lemma interpolation_II_exists:
  forall (j12 j23 j12':meminj) (m1 m1' m2: mem) L2 B
    (VB2_j12: meminj_validblock_2 j12 m2)
      (VB2_j12': meminj_validblock_2' j12' (mem_add_nb m1' m2))
      (INCR: inject_incr j12 j12'),
    exists m2', (forall b ofs, ZMap.get ofs (Mem.mem_contents m2') !! b = 
                                   mem_add_cont j12 j23 j12' m1 m1' m2 L2 B b ofs) /\
                    (forall b, (Mem.mem_access m2') !! b = 
                               mem_add_acc j12 j23 j12' m1 m1' m2 L2 B b) /\  
                    (Mem.nextblock m2' = mem_add_nb m1' m2).
Proof.
  intros.

  (*Access*)
  destruct (acc_construct j12 j23 j12' m1 m1' m2 L2 B VB2_j12 VB2_j12') as
      [mem_access [property_acc [access_max nextblock_noaccess]]].
   
  (*Content*)
  destruct (cont_construct j12 j23 j12' m1 m1' m2 L2 B VB2_j12 VB2_j12' INCR) as
      [mem_contents [property_cont contents_default]].

  exists (Mem.mkmem mem_contents 
                    mem_access
                    (mem_add_nb m1' m2)  (*nextblock*)
                    access_max
                    nextblock_noaccess
                    contents_default).
  simpl; intuition.
Qed.