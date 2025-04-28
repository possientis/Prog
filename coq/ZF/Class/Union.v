Require Import ZF.Axiom.Union.
Require Import ZF.Class.Core.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.

Require Import ZF.Notation.Union.
Export ZF.Notation.Union.

(* The class of all sets x which belongs to some element of P.                  *)
Definition union (P:Class) : Class := fun x =>
  exists y, x :< y /\ P y.

(* Notation ":U( P )" := (union P)                                              *)
Global Instance ClassUnion : Union Class := { union := union }.

(* The union is compatible with class equivalence.                              *)
Proposition EquivCompat : forall (P Q:Class),
  P :~: Q -> :U(P) :~: :U(Q).
Proof.
  intros P Q H1 x. split; intros H2; destruct H2 as [y [H2 H3]];
  exists y; split.
  - assumption.
  - apply H1. assumption.
  - assumption.
  - apply H1. assumption.
Qed.

(* If P is small then U(P) is small.                                            *)
Proposition IsSmall : forall (P:Class),
  Small P -> Small :U(P).
Proof.

  (* Let P be an arbitrary class *)
  intros P.

  (* We assume that P is small *)
  intros H1. assert (Small P) as A. { apply H1. } clear A.

  (* In particular P is equivalent to some set a. *)
  assert (exists a, P :~: toClass a) as H2. { apply Small.IsSomeSet, H1. }

  (* So let a be a set equivalent to the class P. *)
  destruct H2 as [a H2].

  (* We need to show that the union of P is small. *)
  assert (Small :U(P)) as A. 2: apply A.

  (* The property of being small being compatible with equivalences... *)
  apply Small.EquivCompat with :U(toClass a).

  (* We first need to show the equivalence between U(a) and U(P). *)
  - assert (:U(toClass a):~: :U(P)) as A. 2: apply A.

  (* Which follows from the equivalence between a and P. *)
    apply EquivCompat, EquivSym, H2.

  (* We next need to show that U(a) is small. *)
  - assert (Small :U(toClass a)) as A. 2: apply A.

  (* Which follows from the union axiom. *)
    apply ZF.Axiom.Union.Union.
Qed.
