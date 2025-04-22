Require Import ZF.Set.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Union2.

(* The max of two ordinals is equal to one of them.                             *)
Proposition MaxIsLeftOrRight : forall (a b:U), Ordinal a -> Ordinal b ->
  a :\/: b = a \/ a :\/: b = b.
Proof.
  intros a b H1 H2. assert (a :<=: b \/ b :<=: a) as H3. {
    apply InclOrIncl; assumption. }
  destruct H3 as [H3|H3].
  - apply Union2EqualIncl in H3. right. symmetry. assumption.
  - apply Union2EqualIncl in H3. left. symmetry. rewrite Union2Comm. assumption. 
Qed.

(* The max of two ordinals is an ordinal.                                       *)
Proposition MaxIsOrdinal : forall (a b:U), Ordinal a -> Ordinal b ->
  Ordinal (a :\/: b).
Proof.
  intros a b H1 H2. assert (a :\/: b = a \/ a :\/: b = b) as H3. {
    apply MaxIsLeftOrRight; assumption. }
  destruct H3 as [H3|H3]; rewrite H3; assumption.
Qed.
