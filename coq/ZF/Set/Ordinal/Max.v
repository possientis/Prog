Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Union2.

(* The max of two ordinals is equal to one of them.                             *)
Proposition IsLeftOrRight : forall (a b:U), Ordinal a -> Ordinal b ->
  a :\/: b = a \/ a :\/: b = b.
Proof.
  intros a b H1 H2. assert (a :<=: b \/ b :<=: a) as H3. {
    apply InclOrIncl; assumption. }
  destruct H3 as [H3|H3].
  - apply Union2.WhenEqualR in H3. right. symmetry. assumption.
  - apply Union2.WhenEqualR in H3. left. symmetry. rewrite Union2.Comm. assumption.
Qed.

(* The max of two ordinals is an ordinal.                                       *)
Proposition IsOrdinal : forall (a b:U), Ordinal a -> Ordinal b ->
  Ordinal (a :\/: b).
Proof.
  intros a b H1 H2. assert (a :\/: b = a \/ a :\/: b = b) as H3. {
    apply IsLeftOrRight; assumption. }
  destruct H3 as [H3|H3]; rewrite H3; assumption.
Qed.

(* If two ordinals belong to a set, then so does their maximum.                 *)
Proposition ElemCompat : forall (a b c:U), Ordinal a -> Ordinal b ->
  a :< c -> b :< c -> a :\/: b :< c.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c H1 H2 H3 H4.
  (* The maximum of two ordinals is one of the two ordinals.                    *)
  assert (a :\/: b = a \/ a :\/: b = b) as H5. {
    apply IsLeftOrRight; assumption. }
  (* Hence membership of the maximum follows from the corresponding member.     *)
  destruct H5 as [H5|H5]; rewrite H5; assumption.
Qed.

Proposition IsInclL : forall (a b:U),
  a :<=: a :\/: b.
Proof.
  apply Union2.IsInclL.
Qed.

Proposition IsInclR : forall (a b:U),
  b :<=: a :\/: b.
Proof.
  apply Union2.IsInclR.
Qed.
