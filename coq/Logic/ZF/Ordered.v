Declare Scope ZF_Ordered_scope.
Open    Scope ZF_Ordered_scope.

Require Import Logic.ZF.Core.
Require Import Logic.ZF.Pairing.
Require Import Logic.ZF.Singleton.

(* The ordered pair (a,b) is defined as the pair { {a} , {a,b} }.               *)
(* Recall that we use the notation '[a]' for the singleton set {a}.             *)
Definition orderedPair (a b:U) : U := { [a] , {a,b} }.

(* Unfortunately, we cannot use the notation '(a,b)'.                           *)
Notation "(: a , b :)" := (orderedPair a b)
  (at level 1, no associativity) : ZF_Ordered_scope.

(* Characterisation of the elements of (:a,b:).                                 *)
Lemma OrderedCharac : forall (a b:U),
  forall x, x :< (:a,b:) <-> x = [a] \/ x = {a,b}.
Proof.
  intros a b. unfold orderedPair. apply PairCharac.
Qed.

Lemma OrderedABC : forall a b c, [a] = {b,c} -> a = b /\ a = c.
Proof.
  intros a b c Habc. split.
  - symmetry. apply SingleInEqual. rewrite Habc. apply PairAIn.
  - symmetry. apply SingleInEqual. rewrite Habc. apply PairBIn.
Qed.

(* If two ordered pairs are equal, then their components are equal.             *)
Proposition OrderedEqual : forall (a b c d:U),
  (:a,b:) = (:c,d:) -> a = c /\ b = d.
Proof.
  intros a b c d H.
  assert (a = c) as H1.
    { assert ([a] :< (:c,d:)) as H2.
        { rewrite <- H. apply OrderedCharac. left. reflexivity. }
      apply OrderedCharac in H2. destruct H2 as [H2|H2].
      + apply SingleEqualSingle, H2.
      + apply OrderedABC in H2. destruct H2 as [H2 H3]. apply H2. }
  split.
  - apply H1.
  - rewrite <- H1 in H. clear c H1.
    assert ({a,b} :< (:a,d:)) as H1.
      { rewrite <- H. apply OrderedCharac. right. reflexivity. }
    apply OrderedCharac in H1. destruct H1 as [H1|H1].
    + assert (b = a) as H2.
        { apply SingleInEqual. rewrite <- H1. apply PairBIn. }
      subst. clear H1.
      assert ({a,d} :< (:a,a:)) as H1.
        { rewrite H. unfold orderedPair. apply PairBIn. }
      unfold orderedPair in H1. apply PairCharac in H1.
      fold singleton in H1. destruct H1 as [H1|H1].
      * symmetry. apply SingleInEqual. rewrite <- H1. apply PairBIn.
      * symmetry in H1. apply OrderedABC in H1. destruct H1 as [H1 H2]. apply H2.
    + assert (b :< {a,d}) as H2.
        { rewrite <- H1. apply PairBIn. }
      apply PairCharac in H2. destruct H2 as [H2|H2].
      * subst. apply OrderedABC in H1. destruct H1 as [H1 H2]. apply H2.
      * apply H2.
Qed.

Proposition OrderedEqualA : forall (a b c d:U),
  (:a,b:) = (:c,d:) -> a = c.
Proof.
  intros a b d c H. apply OrderedEqual in H. destruct H as [H1 H2]. apply H1.
Qed.

Proposition OrderedEqualB : forall (a b c d:U),
  (:a,b:) = (:c,d:) -> b = d.
Proof.
  intros a b d c H. apply OrderedEqual in H. destruct H as [H1 H2]. apply H2.
Qed.

