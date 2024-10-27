Declare Scope ZF_Tuple_scope.
Open    Scope ZF_Tuple_scope.

Require Import Logic.ZF.Core.
Require Import Logic.ZF.OrdPair.

Definition tuple3 (a1 a2 a3:U) : U := (: (:a1,a2:) , a3 :).

Notation "(: a , b , c :)" := (tuple3 a b c)
  (at level 1, no associativity) : ZF_Tuple_scope.

Definition tuple4 (a1 a2 a3 a4:U) : U := (: (:a1,a2,a3:) , a4 :).

Notation "(: a , b , c , d :)" := (tuple4 a b c d)
  (at level 1, no associativity) : ZF_Tuple_scope.

Proposition Tuple3Equal : forall (a1 a2 a3 b1 b2 b3:U),
  (:a1,a2,a3:) = (:b1,b2,b3:) -> a1 = b1 /\ a2 = b2 /\ a3 = b3.
Proof.
  intros a1 a2 a3 b1 b2 b3 H. apply OrdPairEqual in H.
  destruct H as [H H3]. apply OrdPairEqual in H. destruct H as [H1 H2].
  auto.
Qed.

Proposition Tuple3Equal1 : forall (a1 a2 a3 b1 b2 b3:U),
  (:a1,a2,a3:) = (:b1,b2,b3:) -> a1 = b1.
Proof.
  intros a1 a2 a3 b1 b2 b3 H. apply Tuple3Equal in H.
  destruct H as [H [_ _]]. apply H.
Qed.

Proposition Tuple3Equal2 : forall (a1 a2 a3 b1 b2 b3:U),
  (:a1,a2,a3:) = (:b1,b2,b3:) -> a2 = b2.
Proof.
  intros a1 a2 a3 b1 b2 b3 H. apply Tuple3Equal in H.
  destruct H as [_ [H _]]. apply H.
Qed.

Proposition Tuple3Equal3 : forall (a1 a2 a3 b1 b2 b3:U),
  (:a1,a2,a3:) = (:b1,b2,b3:) -> a3 = b3.
Proof.
  intros a1 a2 a3 b1 b2 b3 H. apply Tuple3Equal in H.
  destruct H as [_ [_ H]]. apply H.
Qed.

Proposition Tuple4Equal : forall (a1 a2 a3 a4 b1 b2 b3 b4:U),
  (:a1,a2,a3,a4:) = (:b1,b2,b3,b4:) -> a1 = b1 /\ a2 = b2 /\ a3 = b3 /\ a4 = b4.
Proof.
  intros a1 a2 a3 a4 b1 b2 b3 b4 H. apply OrdPairEqual in H. destruct H as [H H4].
  apply Tuple3Equal in H. destruct H as [H1 [H2 H3]].
  auto.
Qed.

Proposition Tuple4Equal1 : forall (a1 a2 a3 a4 b1 b2 b3 b4:U),
  (:a1,a2,a3,a4:) = (:b1,b2,b3,b4:) -> a1 = b1.
Proof.
  intros a1 a2 a3 a4 b1 b2 b3 b4 H. apply Tuple4Equal in H.
  destruct H as [H [_ [_ _]]]. apply H.
Qed.

Proposition Tuple4Equal2 : forall (a1 a2 a3 a4 b1 b2 b3 b4:U),
  (:a1,a2,a3,a4:) = (:b1,b2,b3,b4:) -> a2 = b2.
Proof.
  intros a1 a2 a3 a4 b1 b2 b3 b4 H. apply Tuple4Equal in H.
  destruct H as [_ [H [_ _]]]. apply H.
Qed.

Proposition Tuple4Equal3 : forall (a1 a2 a3 a4 b1 b2 b3 b4:U),
  (:a1,a2,a3,a4:) = (:b1,b2,b3,b4:) -> a3 = b3.
Proof.
  intros a1 a2 a3 a4 b1 b2 b3 b4 H. apply Tuple4Equal in H.
  destruct H as [_ [_ [H _]]]. apply H.
Qed.

Proposition Tuple4Equal4 : forall (a1 a2 a3 a4 b1 b2 b3 b4:U),
  (:a1,a2,a3,a4:) = (:b1,b2,b3,b4:) -> a4 = b4.
Proof.
  intros a1 a2 a3 a4 b1 b2 b3 b4 H. apply Tuple4Equal in H.
  destruct H as [_ [_ [_ H]]]. apply H.
Qed.

