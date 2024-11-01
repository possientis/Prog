Declare Scope ZF_Tuple_scope.
Open    Scope ZF_Tuple_scope.

Require Import Logic.ZF.Core.
Require Import Logic.ZF.Pairing.
Require Import Logic.ZF.Singleton.
Require Import Logic.ZF.Union.

Definition tuple3 (a1 a2 a3:U) : U := :{a1,a2}: :\/: :{a3}:.

Notation ":{ a , b , c }:" := (tuple3 a b c)
  (at level 1, no associativity) : ZF_Tuple_scope.

Proposition Tuple3Charac : forall (a1 a2 a3:U),
  forall x, x :< :{a1,a2,a3}: <-> x = a1 \/ x = a2 \/ x = a3.
Proof.
  intros a1 a2 a3 x. unfold tuple3. split.
  - intros H1. apply UnionABCharac in H1. destruct H1 as [H1|H1].
    + apply PairCharac in H1. destruct H1 as [H1|H1].
      * left. apply H1.
      * right. left. apply H1.
    + apply SingleCharac in H1. right. right. apply H1.
  - intros [H1|H1]; apply UnionABCharac.
    + left. apply PairCharac. left. apply H1.
    + destruct H1 as [H1|H1].
      * left. apply PairCharac. right. apply H1.
      * right. apply SingleCharac, H1.
Qed.


