(*Pre-PCM and PCM*)
(*Require Import msl.msl_standard.*)

Class Join (t: Type) : Type := join: t -> t -> t -> Prop.

(* "PrePCM" *)
Class PrePCM (t: Type) {J: Join t} : Type :=
  mkPPCM   {
   join_eq: forall {x y z z'}, join x y z -> join x y z' -> z = z';   
   join_assoc: forall {a b c d e}, join a b d -> join d c e ->
                    {f : t & join b c f /\ join a f e};
   join_comm: forall {a b c}, join a b c -> join b a c
}.

Definition unit_for {t}{J: Join t} (e a: t) := join e a a.
Definition identity {t} {J: Join t} (e: t) := forall a b, join e a b -> a=b.

Class Unital (t: Type) {J: Join t}  : Type :=
  mkUnital {
      join_unit: t;
      join_lid: forall {a},  join join_unit a a
    }.

Class PartialUnital (t: Type) {J: Join t}  : Type :=
  mkPUnital {
      join_pid: forall {a}, exists e, identity e /\ join e a a
    }.

Class PCM (t: Type) {J: Join t}  : Type :=
  mkPCM'   {
      pcm_unital : Unital t;
      pcm_ppcm : PrePCM t
    }.
Existing Instance pcm_ppcm. 
Existing Instance pcm_unital. 
Definition mkPCM {t}{J: Join t} (unit: t) lid eq assoc comm:=
  @mkPCM' _ J (@mkUnital _ J unit lid) (@mkPPCM _ J eq assoc comm).


Set Implicit Arguments.
Module Nats.
(*Nat is pcm*)
Instance join_nat: Join nat:=
  fun a b c => a + b = c.

Lemma lid: forall a,  plus 0 a = a.
  intros a; unfold join, join_nat.
  rewrite plus_O_n; trivial.
Qed.

Lemma lid': @identity _ join_nat O.
  intros a b; unfold join, join_nat.
  rewrite plus_O_n; trivial.
Qed.

Lemma nat_eq: forall x y z z', join_nat x y z -> join_nat x y z' -> z = z'.
  unfold join_nat; intros x y z z' H H'; rewrite <- H, H'. trivial.
Qed.

Lemma nat_assoc: forall a b c d e, join_nat a b d -> join_nat d c e ->
                    {f : nat & join_nat b c f /\ join_nat a f e}.
  intros a b c d e; unfold join_nat; intros H H'.
  exists (b + c); split; auto.
  admit.
Qed.

Lemma nat_comm: forall a b c, join_nat a b c -> join_nat b a c.
  admit.
Qed.

Instance nat_pcm: PCM nat := mkPCM _ lid nat_eq nat_assoc nat_comm.

Module Exports.
  Definition nat_pcm := nat_pcm.
End Exports.
End Nats.
Export Nats.Exports.