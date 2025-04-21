Require Import ZF.Axiom.Classic.
Require Import ZF.Axiom.NonEmptyUniverse.
Require Import ZF.Class.
Require Import ZF.Class.Image.
Require Import ZF.Class.Small.
Require Import ZF.Set.
Require Import ZF.Set.Specify.

Require Import ZF.Notation.Zero.
Export ZF.Notation.Zero.

(* The class which is satisfied by no set.                                      *)
Definition empty : Class := fun _ => False.

(* Notation ":0:" := empty                                                      *)
Global Instance ClassZero : Zero Class := { zero := empty }.

Proposition Charac : forall (x:U), :0: x <-> False.
Proof.
  intros x. unfold zero, ClassZero, empty. split; auto.
Qed.

(* The empty class is small.                                                    *)
Proposition IsSmall : Small :0:.
Proof.
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
  intros x.

  split.
  - intros H3. rewrite H2 in H3. apply SpecifyCharac in H3.
    destruct H3 as [H3 H4]. contradiction.
  - intros H3. contradiction.
Qed.

Proposition NotEmptyHasElem : forall (P:Class),
  P :<>: :0: <-> exists x, P x.
Proof.
  intros P. split; intros H1.
  - apply NotForAllNot. intros H2. apply H1. intros x. split; intros H3.
    + apply Charac, (H2 x), H3.
    + apply Charac in H3. contradiction.
  - destruct H1 as [x H1]. intros H2. apply H2, Charac in H1. contradiction.
Qed.

Proposition EmptyImage : forall (P Q:Class),
  Q :~: :0: -> P:[Q]: :~: :0:.
Proof.
  intros P Q H1 y. split; intros H2.
  - destruct H2 as [x [H2 H3]]. apply H1 in H2. apply Charac in H2. contradiction.
  - apply Charac in H2. contradiction.
Qed.
