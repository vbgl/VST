Require Import compcert.lib.Coqlib.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Events.

(*From mem_lemmas*)
Notation val_inject:= Val.inject.

Definition mem_forward (m1 m2:mem) :=
  forall b (B:Mem.valid_block m1 b),
    Mem.valid_block m2 b
    /\ (forall ofs p, Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p).

Definition LocsetB:Type := block -> Z -> bool.
Definition Locset:Type := block -> Z -> Prop.

(** * Simulations *)
Definition Blockset:Type := block -> bool.

(*Require Import VST.sepcomp.mem_lemmas.*)
Lemma valid_block_dec: forall m b, {Mem.valid_block m b} +  {~Mem.valid_block m b}.
Proof. intros.
unfold Mem.valid_block.
remember (plt b (Mem.nextblock m)).
destruct s. left; assumption.
right. intros N. xomega.
Qed.

Definition freshblockB m m' b:bool := valid_block_dec m' b && negb (valid_block_dec m b).
Definition freshblock m m' b:Prop := Mem.valid_block m' b /\ ~ Mem.valid_block m b.

(*If SRC-writes are confined to X, TGT-writes are confined to locations in the j-image of X and local blocks*)
Definition write_confined m1 m1' (j:meminj) (LT:Blockset) m2 m2':Prop :=
   forall (X:Locset) (HX: forall b z (Hb1: Mem.valid_block m1 b), 
                          Mem.unchanged_on (fun b' z' => (b',z')=(b,z)) m1 m1' \/ X b z)
          b2 z (Hz: Mem.valid_block m2 b2), 
   Mem.unchanged_on (fun bb zz => (bb,zz)=(b2,z)) m2 m2' \/
   LT b2 = true (*could probably be strengthened to LT b2 - true /\ loc_out_of_reach j m1' b2 z*) \/
   (exists b1 d, j b1 = Some(b2,d) /\ X b1 (z-d)).

(*If SRC-writes are confined to X, TGT-writes are confined to locations in X and local blocks*)
Definition write_confinedExt m1 m1' (L:Blockset) m2 m2':Prop :=
   forall (X:Locset) (HX: forall b z (Hb1: Mem.valid_block m1 b), 
                          Mem.unchanged_on (fun b' z' => (b',z')=(b,z)) m1 m1' \/ X b z)
          b2 z (Hz: Mem.valid_block m2 b2), 
   Mem.unchanged_on (fun bb zz => (bb,zz)=(b2,z)) m2 m2' \/ L b2 = true \/ X b2 z.

(*
Definition lsep m (j j':meminj) := forall b1 b2 d, j b1 = None -> 
   j' b1 = Some (b2,d) -> ~Mem.valid_block m b1.*)
Definition isep m1 (j j':meminj) m2 (LT:Blockset) := forall b1 b2 d 
           (J:j b1 = None) (J':j' b1 = Some (b2,d)),
           ~Mem.valid_block m1 b1 /\ (Mem.valid_block m2 b2 -> LT b2 = true).
Definition esep m1 (j j':meminj) m2 (LT:Blockset) := forall b1 b2 d 
           (J:j b1 = None) (J':j' b1 = Some (b2,d)),
           ~Mem.valid_block m1 b1 /\ (Mem.valid_block m2 b2 -> LT b2 = false).

Definition full_comp (j1 j2: meminj) :=
  forall b0 b1 delta1, j1 b0 = Some (b1, delta1) -> exists b2 delta2, j2 b1 = Some (b2, delta2).

Definition genv2blocksBool {F V : Type} (ge : Genv.t F V):=
  (fun b =>
      match Genv.invert_symbol ge b with
        Some id => true
      | None => false
      end,
   fun b => match Genv.find_var_info ge b with
                  Some gv => true
                | None => false
            end).

Definition isGlobalBlock {F V : Type} (ge : Genv.t F V) :=
  fun b => (fst (genv2blocksBool ge)) b || (snd (genv2blocksBool ge)) b.

Definition globals_separate {F V:Type} (ge: Genv.t F V) (j j': meminj) :=
    forall b1 b2 d, j b1 = None -> j' b1 =Some(b2,d) ->
           isGlobalBlock ge b2 = false.

Definition globals_preserved {F1 V1 F2 V2:Type} (ge1: Genv.t F1 V1) (ge2: Genv.t F2 V2) (j:meminj) :=
 forall b1 b2 d, j b1 = Some(b2,d) -> isGlobalBlock ge1 b1 = isGlobalBlock ge2 b2.

Definition globals_valid {F V:Type} (ge: Genv.t F V) (m:mem):=
 forall b, isGlobalBlock ge b = true -> Mem.valid_block m b.

Definition ReadOnlyBlocks {F V} (ge: Genv.t F V) (b:block): bool :=
  match Genv.find_var_info ge b with
          None => false
        | Some gv => gvar_readonly gv && negb (gvar_volatile gv)
  end.

Definition readonly m1 b m2 :=
    forall n ofs (NWR: forall i, 0 <= i < n -> ~(Mem.perm m1 b (ofs + i) Cur Writable)),
     Mem.loadbytes m2 b ofs n = Mem.loadbytes m1 b ofs n /\
     (forall i, 0 <= i < n -> (forall k p, Mem.perm m1 b (ofs+i) k p <-> Mem.perm m2 b (ofs+i) k p)).

Definition RDOnly_fwd (m1 m1':mem) B :=
  forall b (Hb: B b = true), readonly m1 b m1'.

Definition mem_respects_readonly {F V} (ge : Genv.t F V) m :=
    forall b gv, Genv.find_var_info ge b = Some gv ->
                 gvar_readonly gv && negb (gvar_volatile gv) = true ->
           Genv.load_store_init_data ge m b 0 (gvar_init gv) /\
           Mem.valid_block m b /\ (forall ofs : Z, ~ Mem.perm m b ofs Max Writable).

Definition forward {F V:Type} (ge:Genv.t F V) m1 m2 := mem_forward m1 m2
    /\ RDOnly_fwd m1 m2 (ReadOnlyBlocks ge).


Definition full_ext  (LS: Blockset) (j1 j2: meminj):=
  forall b1 b2 delta1, j1 b1 = Some (b2, delta1) -> LS b1 = false ->
  exists b3 delta2, j2 b2 = Some (b3, delta2).