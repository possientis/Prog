Require Import ZF.Axiom.Classic.
Require Import ZF.Axiom.Extensionality.
Require Import ZF.Axiom.NonEmptyUniverse.
Require Import ZF.Class.Small.
Require Import ZF.Core.Leq.
Require Import ZF.Core.Zero.
Require Import ZF.Set.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.Incl.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Pair.
Require Import ZF.Set.Singleton.
Require Import ZF.Set.Specify.

(* The class which is satisfied by no set.                                      *)
Definition Empty : U -> Prop := fun _ => False.

(* The empty class is small.                                                    *)
Proposition EmptySmall : Small Empty.
Proof.
  unfold Small, Empty.

  (* We know there is at least one set in the universe *)
  remember NonEmptyUniverse as H1 eqn:A. clear A.

  (* Let a be such a set *)
  destruct H1 as [a _].

  (* We need to show the existence of a set b with no elements *)
  assert (exists b, forall x, x :< b <-> False) as A. 2: apply A.

  (* Consider the set b = { x | x :< a /\ ~ x :< a } *)
  remember :{a | fun x => ~ x :< a }: as b eqn:H2.

  (* We claim this set b has the required property *)
  exists b.

  (* We need to show that x :< b <-> False for all x *)
  assert (forall x, x :< b <-> False) as A. 2: apply A.

  (* So let x be an arbitrary set *)
  intros x. split.

  (* Proof of -> *)
  - intros H3. rewrite H2 in H3. apply SpecCharac in H3.
    destruct H3 as [H3 H4]. contradiction.

  (* Proof of <- *)
  - intros H3. contradiction.
Qed.

(* We consider the set defined by the small class Empty                         *)
Definition emptySet : U := fromClass Empty EmptySmall.

(* Notation ":0:" := emptySet                                                   *)
Global Instance SetZero : Zero U := { zero := emptySet }.

(* Characterisation of the elements of the empty set.                           *)
Proposition EmptyCharac : forall x, x :< :0: <-> False.
Proof.
  unfold emptySet. apply FromClassCharac.
Qed.

(* The empty set has no element.                                                *)
Proposition EmptySetEmpty : forall x, ~ x :< :0:.
Proof.
  intros x H1. apply EmptyCharac in H1. apply H1.
Qed.

(* If a set is not empty, then it has an element.                               *)
Proposition NotEmptyHasElement : forall (a:U),
  ~ a = :0: <-> exists x, x :< a.
Proof.
  intros a. split; intros H1.
  - apply NotForAllNot. intros H2. apply H1, Extensionality.
    intros x. split; intros H3.
    + apply EmptyCharac, (H2 x), H3.
    + apply EmptyCharac in H3. contradiction.
  - destruct H1 as [x H1]. intros H2. rewrite H2 in H1.
    apply EmptyCharac in H1. apply H1.
Qed.

Proposition IfEmptyThenEmpty : forall (a:U),
  (forall x, ~ x :< a) -> a = :0:.
Proof.
  intros a Ha. apply Extensionality. intros x. split; intros H1.
  - apply (Ha x) in H1. contradiction.
  - apply EmptyCharac in H1. contradiction.
Qed.

(* A pair is never equal to the empty set.                                      *)
Proposition PairNotEmpty : forall (a b:U), ~ :{a,b}: = :0:.
Proof.
  intros a b Hab. assert (a :< :0:) as H1. { rewrite <- Hab. apply PairInL. }
  apply EmptyCharac in H1. apply H1.
Qed.

(* The empty set is not an ordered pair                                         *)
Proposition OrdPairNotEmpty : forall (x y:U), ~ :(x,y): = :0:.
Proof.
  intros x y H1. apply DoubleInclusion in H1. destruct H1 as [H1 _].
  apply EmptySetEmpty with :{x}:. apply H1, PairInL.
Qed.

Proposition SingletonNotEmpty : forall a, ~ :{a}: = :0:.
Proof.
  intros a. apply PairNotEmpty.
Qed.
