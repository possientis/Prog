Require Import ZF.Class.Equiv.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Pair.
Require Import ZF.Set.Union.

Require Import ZF.Notation.Or.
Export ZF.Notation.Or.

(* The class of all sets x which belong to P or belong to Q.                    *)
Definition union2 (P Q:Class) : Class := fun x => P x \/ Q x.

(* Notation "P :\/: Q" := (union P Q)                                           *)
Global Instance ClassOr : Or Class := { or := union2 }.

(* Pairwise union is compatible with class equivalence.                         *)
Proposition EquivCompat : forall (P Q R S:Class),
  P :~: Q -> R :~: S -> P :\/: R :~: Q :\/: S.
Proof.
  intros P Q R S H1 H2 x. split; intros H3;
  destruct H3 as [H3|H3].
  - left. apply H1. assumption.
  - right. apply H2. assumption.
  - left. apply H1. assumption.
  - right. apply H2. assumption.
Qed.

(* Pairwise union is left-compatible with class equivalence.                    *)
Proposition EquivCompatL : forall (P Q R:Class),
  P :~: Q -> P :\/: R :~: Q :\/: R.
Proof.
  intros P Q R H1. apply EquivCompat.
  - assumption.
  - apply Equiv.Refl.
Qed.

(* Pairwise union is right-compatible with class equivalence.                   *)
Proposition EquivCompatR : forall (P Q R:Class),
  P :~: Q -> R :\/: P :~: R :\/: Q.
Proof.
  intros P Q R H1. apply EquivCompat.
  - apply Equiv.Refl.
  - assumption.
Qed.

(* Thw pairwise union of two small classes is a small class.                    *)
Proposition IsSmall : forall (P Q:Class),
  Small P -> Small Q -> Small (P :\/: Q).
Proof.

  (* Let P and Q be arbitrary classes *)
  intros P Q.

  (* We assume that P is small *)
  intros H1. assert (Small P) as A. { apply H1. } clear A.

  (* Amd we assume that Q is small *)
  intros H2. assert (Small Q) as A. { apply H2. } clear A.

  (* P is equivalent to some set a. *)
  assert (exists a, P :~: toClass a) as H3. { apply Small.IsSomeSet, H1. }

  (* Q is equivalent to some set b. *)
  assert (exists b, Q :~: toClass b) as H4. { apply Small.IsSomeSet, H2. }

  (* So let a be a set equivalent to the class P. *)
  destruct H3 as [a H3].

  (* And let b be a set equivalent to the class Q. *)
  destruct H4 as [b H4].

  (* We need to show that the union of P and Q is small. *)
  assert (Small (P :\/: Q)) as A. 2: apply A.

  (* The property of being small being compatible with equivalences... *)
  apply Small.EquivCompat with (toClass a :\/: toClass b).

  (* We first need to show the equivalence between P \/ Q and a \/ b. *)
  - assert (toClass a :\/: toClass b :~: P :\/: Q) as A. 2: apply A.

  (* Which follows from the equivalences of a and P and  of b and Q. *)
    apply EquivCompat; apply Equiv.Sym; assumption.

  (* We next need to show that a \/ b is small. *)
  - assert (Small (toClass a :\/: toClass b)) as A. 2: apply A.

  (* In other words we need to show the existence of a set c with the right property *)
    assert (exists c, forall x, x :< c <-> x :< a \/ x :< b) as A. 2: apply A.

  (* Consider the set c = U({a,b}). *)
    remember (:U(:{a,b}:)) as c eqn:Ec.

  (* We claim that c has the desired property *)
    exists c.

  (* So given an arbitrary set x... *)
    intros x.

  (* We need to show that x :< c iff x :< a or x :< b. *)
    assert (x :< c <-> x :< a \/ x :< b) as A. 2: apply A.

    split; intros H5.
    + rewrite Ec in H5. apply Union.Charac in H5. destruct H5 as [y [H5 H6]].
      apply Pair.Charac in H6. destruct H6 as [H6|H6]; subst.
      * left.  assumption.
      * right. assumption.
    + rewrite Ec. apply Union.Charac. destruct H5 as [H5|H5].
      * exists a. split. { assumption. } { apply Pair.IsInL. }
      * exists b. split. { assumption. } { apply Pair.IsInR. }
Qed.
