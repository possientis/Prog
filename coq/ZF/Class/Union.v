Require Import ZF.Axiom.Union.
Require Import ZF.Class.
Require Import ZF.Class.Small.
Require Import ZF.Core.Equiv.
Require Import ZF.Core.Union.
Require Import ZF.Set.

(* The union class of a class.                                                  *)
Definition union (P:Class) : Class := fun x =>
  exists y, x :< y /\ P y.

(* Notation ":U( P )" := (union P)                                              *)
Global Instance ClassUnion : Union Class := { union := union }.

Proposition UnionCharac : forall (P:Class) (x:U),
  :U(P) x <-> exists y, x :< y /\ P y.
Proof.
  intros P a. unfold Core.Union.union, ClassUnion, union. split; auto.
Qed.

Proposition UnionEquivCompat : forall (P Q:Class),
  P :~: Q -> :U(P) :~: :U(Q).
Proof.
  intros P Q H1 x. split; intros H2;
  apply (proj1 (UnionCharac _ _)) in H2; destruct H2 as [y [H2 H3]];
  apply UnionCharac; exists y; split.
  - assumption.
  - apply H1. assumption.
  - assumption.
  - apply ClassEquivSym in H1. apply H1. assumption.
Qed.

(* If P is small then U(P) is small.                                            *)
Proposition UnionIsSmall : forall (P:Class),
  Small P -> Small :U(P).
Proof.

  (* Let P be an arbitrary class *)
  intros P.

  (* We assume that P is small *)
  intros H1. assert (Small P) as A. { apply H1. } clear A.

  (* In particular P is equivalent to some set a. *)
  assert (exists a, toClass a :~: P) as H2.
    { apply (proj1 (SmallIsSomeSet _)), H1. }

  (* So let a be a set equivalent to the class P. *)
  destruct H2 as [a H2].

  (* We need to show that the union of P is small. *)
  assert (Small :U(P)) as A. 2: apply A.

  (* The property of being small being compatible with equivalences... *)
  apply SmallEquivCompat with :U(toClass a).

  (* We first need to show the equivalence between U(a) and U(P). *)
  - assert (:U(toClass a):~: :U(P)) as A. 2: apply A.

  (* Which follows from the equivalence between a and P. *)
    apply UnionEquivCompat, H2.

  (* We next need to show that U(a) is small. *)
  - assert (Small :U(toClass a)) as A. 2: apply A.

  (* Which follows from the union axiom. *)
    apply ZF.Axiom.Union.Union.
Qed.
