Declare Scope ZF_Set_Tuple_scope.
Open    Scope ZF_Set_Tuple_scope.

Require Import ZF.Class.
Require Import ZF.Class.Incl.
Require Import ZF.Set.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Pair.
Require Import ZF.Set.Singleton.
Require Import ZF.Set.Union2.

Definition tuple3 (a1 a2 a3:U) : U := :{a1,a2}: :\/: :{a3}:.

Notation ":{ a , b , c }:" := (tuple3 a b c)
  (at level 1, no associativity) : ZF_Set_Tuple_scope.

Definition tuple4 (a1 a2 a3 a4:U) : U := :{a1,a2,a3}: :\/: :{a4}:.

Notation ":{ a , b , c , d }:" := (tuple4 a b c d)
  (at level 1, no associativity) : ZF_Set_Tuple_scope.

Proposition Tuple3Charac : forall (a1 a2 a3:U),
  forall x, x :< :{a1,a2,a3}: <-> x = a1 \/ x = a2 \/ x = a3.
Proof.
  intros a1 a2 a3 x. unfold tuple3. split.
  - intros H1. apply Union2Charac in H1. destruct H1 as [H1|H1].
    + apply PairCharac in H1. destruct H1 as [H1|H1]; auto.
    + apply SingleCharac in H1. auto.
  - intros [H1|[H1|H1]]; apply Union2Charac; subst.
    + left. apply PairInL.
    + left. apply PairInR.
    + right. apply SingleIn.
Qed.

Proposition Tuple3EqualIn1 : forall (a1 a2 a3:U),
  forall x, x = a1 -> x :< :{a1,a2,a3}:.
Proof.
  intros a1 a2 a3 x Hx. apply Tuple3Charac. left. apply Hx.
Qed.

Proposition Tuple3EqualIn2 : forall (a1 a2 a3:U),
  forall x, x = a2 -> x :< :{a1,a2,a3}:.
Proof.
  intros a1 a2 a3 x Hx. apply Tuple3Charac. right. left. apply Hx.
Qed.

Proposition Tuple3EqualIn3 : forall (a1 a2 a3:U),
  forall x, x = a3 -> x :< :{a1,a2,a3}:.
Proof.
  intros a1 a2 a3 x Hx. apply Tuple3Charac. right. right. apply Hx.
Qed.

Proposition Tuple3In1 : forall (a1 a2 a3:U), a1 :< :{a1,a2,a3}:.
Proof.
  intros a1 a2 a3. apply Tuple3EqualIn1. reflexivity.
Qed.

Proposition Tuple3In2 : forall (a1 a2 a3:U), a2 :< :{a1,a2,a3}:.
Proof.
  intros a1 a2 a3. apply Tuple3EqualIn2. reflexivity.
Qed.

Proposition Tuple3In3 : forall (a1 a2 a3:U), a3 :< :{a1,a2,a3}:.
Proof.
  intros a1 a2 a3. apply Tuple3EqualIn3. reflexivity.
Qed.

Proposition Tuple4Charac : forall (a1 a2 a3 a4:U),
  forall x, x :< :{a1,a2,a3,a4}: <-> x = a1 \/ x = a2 \/ x = a3 \/ x = a4.
Proof.
  intros a1 a2 a3 a4 x. unfold tuple4. split.
  - intros H1. apply Union2Charac in H1. destruct H1 as [H1|H1].
    + apply Tuple3Charac in H1. destruct H1 as [H1|[H1|H1]]; auto.
    + apply SingleCharac in H1. auto.
  - intros [H1|[H1|[H1|H1]]]; apply Union2Charac.
    + left. apply Tuple3EqualIn1, H1.
    + left. apply Tuple3EqualIn2, H1.
    + left. apply Tuple3EqualIn3, H1.
    + right. apply SingleCharac, H1.
Qed.

Proposition Tuple4EqualIn1 : forall (a1 a2 a3 a4:U),
  forall x, x = a1 -> x :< :{a1,a2,a3,a4}:.
Proof.
  intros a1 a2 a3 a4 x Hx. apply Tuple4Charac. left. apply Hx.
Qed.

Proposition Tuple4EqualIn2 : forall (a1 a2 a3 a4:U),
  forall x, x = a2 -> x :< :{a1,a2,a3,a4}:.
Proof.
  intros a1 a2 a3 a4 x Hx. apply Tuple4Charac. right. left. apply Hx.
Qed.

Proposition Tuple4EqualIn3 : forall (a1 a2 a3 a4:U),
  forall x, x = a3 -> x :< :{a1,a2,a3,a4}:.
Proof.
  intros a1 a2 a3 a4 x Hx. apply Tuple4Charac. right. right. left. apply Hx.
Qed.

Proposition Tuple4EqualIn4 : forall (a1 a2 a3 a4:U),
  forall x, x = a4 -> x :< :{a1,a2,a3,a4}:.
Proof.
  intros a1 a2 a3 a4 x Hx. apply Tuple4Charac. right. right. right. apply Hx.
Qed.

Proposition Tuple4In1 : forall (a1 a2 a3 a4:U), a1 :< :{a1,a2,a3,a4}:.
Proof.
  intros a1 a2 a3 a4. apply Tuple4EqualIn1. reflexivity.
Qed.

Proposition Tuple4In2 : forall (a1 a2 a3 a4:U), a2 :< :{a1,a2,a3,a4}:.
Proof.
  intros a1 a2 a3 a4. apply Tuple4EqualIn2. reflexivity.
Qed.

Proposition Tuple4In3 : forall (a1 a2 a3 a4:U), a3 :< :{a1,a2,a3,a4}:.
Proof.
  intros a1 a2 a3 a4. apply Tuple4EqualIn3. reflexivity.
Qed.

Proposition Tuple4In4 : forall (a1 a2 a3 a4:U), a4 :< :{a1,a2,a3,a4}:.
Proof.
  intros a1 a2 a3 a4. apply Tuple4EqualIn4. reflexivity.
Qed.

Proposition Tuple3NotEmpty : forall (a1 a2 a3:U), :{a1,a2,a3}: <> :0:.
Proof.
  intros a1 a2 a3 H1. assert (a1 :< :0:) as H2. { rewrite <- H1. apply Tuple3In1. }
  apply EmptyCharac in H2. apply H2.
Qed.

Proposition Tuple4NotEmpty : forall (a1 a2 a3 a4:U), :{a1,a2,a3,a4}: <> :0:.
Proof.
  intros a1 a2 a3 a4 H1. assert (a1 :< :0:) as H2. { rewrite <- H1. apply Tuple4In1. }
  apply EmptyCharac in H2. apply H2.
Qed.

Proposition Tuple3ToClassIncl : forall (A:Class) (a1 a2 a3:U),
  A a1 /\ A a2 /\ A a3 <-> toClass :{a1,a2,a3}: :<=: A.
Proof.
  intros A a1 a2 a3. split; intros H1.
  - destruct H1 as [H1 [H2 H3]]. intros x H4. apply Tuple3Charac in H4.
    destruct H4 as [H4|[H4|H4]]; subst; assumption.
  - split. 1: apply H1, Tuple3In1.
    split. 1: apply H1, Tuple3In2.
    apply H1, Tuple3In3.
Qed.

Proposition Tuple4ToClassIncl : forall (A:Class) (a1 a2 a3 a4:U),
  A a1 /\ A a2 /\ A a3 /\ A a4 <-> toClass :{a1,a2,a3,a4}: :<=: A.
Proof.
  intros A a1 a2 a3 a4. split; intros H1.
  - destruct H1 as [H1 [H2 [H3 H4]]]. intros x H5. apply Tuple4Charac in H5.
    destruct H5 as [H5|[H5|[H5|H5]]]; subst; assumption.
  - split. 1: apply H1, Tuple4In1.
    split. 1: apply H1, Tuple4In2.
    split. 1: apply H1, Tuple4In3.
    apply H1, Tuple4In4.
Qed.
