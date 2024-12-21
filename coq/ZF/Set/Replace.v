Require Import ZF.Axiom.Replacement.
Require Import ZF.Binary.
Require Import ZF.Binary.Functional.
Require Import ZF.Binary.Image.
Require Import ZF.Class.
Require Import ZF.Class.Small.
Require Import ZF.Core.Equiv.
Require Import ZF.Core.Image.
Require Import ZF.Set.

(* It is useful to define the class underlying the replacement axiom.           *)
Definition ReplacePred (F:Binary) (P:Class) : Class := fun y =>
  exists x, P x /\ F x y.

(* This class is exactly F[P], the direct image of P by F.                      *)
Proposition ReplacePredImage : forall (F:Binary) (P:Class),
    ReplacePred F P :~: F:[P]:.
Proof.
  intros F P y. split; auto.
Qed.

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

  (* We need to show that the direct image of P by F is small. *)
  assert (Small F:[P]:) as A. 2: apply A.
Admitted.

(* The set defined by the class F[P] when F is functional and P is small.       *)
Definition replaceSet (F:Binary) (P:Class) (p:Functional F) (q:Small P) : U
  := toSet F:[P]: (ReplaceSmall F P p q).

(* Characterisation of the elements of the replace set of F P.                  *)
Proposition ReplaceCharac : forall (F:Binary)(P:Class)(p:Functional F)(q:Small P),
  forall y, y :< (replaceSet F P p q) <-> F:[P]: y.
Proof.
  unfold replaceSet. intros F P p q. apply ClassCharac.
Qed.
