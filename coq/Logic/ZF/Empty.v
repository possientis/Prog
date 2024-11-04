Declare Scope ZF_Empty_scope.
Open    Scope ZF_Empty_scope.

Require Import Logic.ZF.Class.
Require Import Logic.ZF.Classic.
Require Import Logic.ZF.Comprehension.
Require Import Logic.ZF.Core.
Require Import Logic.ZF.Extensionality.

(* This axiom is not necessary as the axiom of infinity also asserts the        *)
(* the existence of at least one set. However, it allows us to define the empty *)
(* set now and rewrite more concisely the axiom of infinity later.              *)
Axiom NonEmptyUniverse : exists (x:U), True.

(* The class which is satisfied by no set.                                      *)
Definition Empty : Class := fun _ => False.

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
  - intros H3. rewrite H2 in H3. apply CompCharac in H3.
    destruct H3 as [H3 H4]. contradiction.

  (* Proof of <- *)
  - intros H3. contradiction.
Qed.

(* We consider the set defined by the small class Empty                         *)
Definition emptySet : U := toSet Empty EmptySmall.

Notation ":0:" := emptySet
  (at level 0, no associativity) : ZF_Empty_scope.

(* Characterisation of the elements of the empty set.                           *)
Proposition EmptyCharac : forall x, x :< :0: <-> False.
Proof.
  unfold emptySet. apply ClassCharac.
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

