Declare Scope ZF_Set_OrdPair_scope.
Open    Scope ZF_Set_OrdPair_scope.

Require Import ZF.Set.Core.
Require Import ZF.Set.Pair.
Require Import ZF.Set.Singleton.

(* The ordered pair (a,b) is defined as the pair { {a} , {a,b} }.               *)
Definition ordPair (a b:U) : U := :{ :{a}: , :{a,b}: }:.

(* Unfortunately, we cannot use the notation '(a,b)'.                           *)
Notation ":( a , b ):" := (ordPair a b)
  (at level 1, no associativity) : ZF_Set_OrdPair_scope.

(* Characterisation of the elements of (:a,b:).                                 *)
Lemma Charac : forall (a b:U),
  forall x, x :< :(a,b): <-> x = :{a}: \/ x = :{a,b}:.
Proof.
  intros a b. unfold ordPair. apply Pair.Charac.
Qed.

Lemma ABC : forall a b c, :{a}: = :{b,c}: -> a = b /\ a = c.
Proof.
  intros a b c Habc. split.
  - symmetry. apply SingleCharac. rewrite Habc. apply Pair.InL.
  - symmetry. apply SingleCharac. rewrite Habc. apply Pair.InR.
Qed.

(* If two ordered pairs are equal, then their components are equal.             *)
Proposition WhenEqual : forall (a b c d:U),
  :(a,b): = :(c,d): -> a = c /\ b = d.
Proof.
  intros a b c d H.
  assert (a = c) as H1.
    { assert (:{a}: :< :(c,d):) as H2.
        { rewrite <- H. apply Charac. left. reflexivity. }
      apply Charac in H2. destruct H2 as [H2|H2].
      + apply SingleEqualSingle, H2.
      + apply ABC in H2. destruct H2 as [H2 H3]. apply H2. }
  split.
  - apply H1.
  - rewrite <- H1 in H. clear c H1.
    assert (:{a,b}: :< :(a,d):) as H1.
      { rewrite <- H. apply Charac. right. reflexivity. }
    apply Charac in H1. destruct H1 as [H1|H1].
    + assert (b = a) as H2.
        { apply SingleCharac. rewrite <- H1. apply Pair.InR. }
      subst. clear H1.
      assert (:{a,d}: :< :(a,a):) as H1.
        { rewrite H. unfold ordPair. apply Pair.InR. }
      unfold ordPair in H1. apply Pair.Charac in H1.
      fold singleton in H1. destruct H1 as [H1|H1].
      * symmetry. apply SingleCharac. rewrite <- H1. apply Pair.InR.
      * symmetry in H1. apply ABC in H1. destruct H1 as [H1 H2]. apply H2.
    + assert (b :< :{a,d}:) as H2.
        { rewrite <- H1. apply Pair.InR. }
      apply Pair.Charac in H2. destruct H2 as [H2|H2].
      * subst. apply ABC in H1. destruct H1 as [H1 H2]. apply H2.
      * apply H2.
Qed.

Proposition WhenEqualL : forall (a b c d:U),
  :(a,b): = :(c,d): -> a = c.
Proof.
  intros a b d c H. apply WhenEqual in H. destruct H as [H1 H2]. apply H1.
Qed.

Proposition WhenEqualR : forall (a b c d:U),
  :(a,b): = :(c,d): -> b = d.
Proof.
  intros a b d c H. apply WhenEqual in H. destruct H as [H1 H2]. apply H2.
Qed.

