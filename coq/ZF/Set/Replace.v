Require Import ZF.Axiom.Replacement.
Require Import ZF.Binary.
Require Import ZF.Binary.Functional.
Require Import ZF.Binary.Image.
Require Import ZF.Class.
Require Import ZF.Class.Small.
Require Import ZF.Core.Equiv.
Require Import ZF.Core.Image.
Require Import ZF.Set.
Require Import ZF.Set.FromClass.

(* If F is functional and P is small, then F:[P]: is small                      *)
Proposition ReplaceSmall : forall (F:Binary) (P:Class),
  Functional F -> Small P -> Small F:[P]:.
Proof.

  (* Let F be a binary class and P be a class. *)
  intros F P.

  (* We assume that F is functional. *)
  intros H1. assert (Functional F) as A. { apply H1. } clear A.

  (* We assume that P is small. *)
  intros H2. assert (Small P) as A. { apply H2. } clear A.

  (* In particular P is equivalent to some set a. *)
  assert (exists a, toClass a :~: P) as H3. { apply (proj1 (SmallIsSet _)), H2. }

  (* So let a be a set equivalent to the class P. *)
  destruct H3 as [a H3].

  (* We need to show that the direct image of P by F is small. *)
  assert (Small F:[P]:) as A. 2: apply A.

  (* The property of being small being compatible with equivalences... *)
  apply SmallEquivCompat with F:[toClass a]:.

  (* We first need to show the equivalence between F[a] and F[P]. *)
  - assert (F:[toClass a]: :~: F:[P]:) as A. 2: apply A.

  (* Which follows from the equivalence between a and P. *)
  apply ImageEquivCompatR, H3.

  (* We next need to show that F[a] is small. *)
  - assert (Small F:[toClass a]:) as A. 2: apply A.

  (* Which follows from the replacement axiom and the fact F is functional. *)
    apply Replacement, H1.
Qed.

(* The set defined by the class F[P] when F is functional and P is small.       *)
Definition replaceSet (F:Binary) (P:Class) (p:Functional F) (q:Small P) : U
  := fromClass F:[P]: (ReplaceSmall F P p q).

(* Characterisation of the elements of the set associated with the class F[P].  *)
Proposition ReplaceCharac : forall (F:Binary)(P:Class)(p:Functional F)(q:Small P),
  forall y, y :< (replaceSet F P p q) <-> F:[P]: y.
Proof.
  unfold replaceSet. intros F P p q. apply FromClassCharac.
Qed.
