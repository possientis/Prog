Declare Scope ZF_Set_Singleton_scope.
Open    Scope ZF_Set_Singleton_scope.

Require Import ZF.Class.Core.
Require Import ZF.Class.Incl.
Require Import ZF.Set.Core.
Require Import ZF.Set.Pair.

(* The singleton set {a} is defined as the pair {a,a}.                          *)
Definition singleton (a:U) : U := :{a,a}:.

Notation ":{ a }:" := (singleton a)
  (at level 1, no associativity) : ZF_Set_Singleton_scope.

(* Characterisation of the elements of {a}.                                     *)
Proposition SingleCharac : forall (a:U),
  forall x, x :< :{a}: <-> x = a.
Proof.
  intros a x. split.
  - intros Hx. apply PairCharac in Hx. destruct Hx as [Hx|Hx]; apply Hx.
  - intros Hx. apply PairCharac. left. apply Hx.
Qed.

(* The set a is an element of the singleton set [a].                            *)
Proposition SingleIn : forall a, a :< :{a}:.
Proof.
  intros a. apply SingleCharac. reflexivity.
Qed.

Proposition SingleEqualSingle : forall a b, :{a}: = :{b}: -> a = b.
Proof.
  intros a b Hab. apply SingleCharac. rewrite <- Hab.
  apply SingleCharac. reflexivity.
Qed.

Proposition SingleToClassIncl : forall (A:Class) (a:U),
  A a <-> toClass :{a}: :<=: A.
Proof.
  intros A a. split; intros H1.
  - intros x H2. apply SingleCharac in H2. subst. assumption.
  - apply H1. apply SingleIn.
Qed.

Proposition SingleIsNotPair : forall (a b c:U),
  b <> c -> :{a}: <> :{b,c}:.
Proof.
  intros a b c H1 H2.
  assert (b = a) as H3. { apply SingleCharac. rewrite H2. apply PairInL. }
  assert (c = a) as H4. { apply SingleCharac. rewrite H2. apply PairInR. }
  subst. contradiction.
Qed.
