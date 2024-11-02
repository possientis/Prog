Require Import Logic.ZF.ClassRel.
Require Import Logic.ZF.Class.
Require Import Logic.ZF.Core.

(* Given a functional class relation F and a set a, there exist a set b whose   *)
(* elements are the images of the elements of a by F.                           *)
Axiom Replacement : forall (F:ClassRel), Functional F ->
  forall a, exists b, forall y, y :< b <-> exists x, x :< a /\ F x y.

(* It is useful to define the predicate underlying the replacement axiom.       *)
Definition ReplacePred (F:ClassRel) (a:U) : U -> Prop := fun y =>
  exists x, x :< a /\ F x y.

(* This predicate is exactly F[a], the direct image of a by F.                  *)
Proposition ReplacePredImage : forall (F:ClassRel) (a:U) (y:U),
    ReplacePred F a y <-> F[a] y.
Proof.
  intros F a y. split; auto.
Qed.

(* If F is functional then F[a] is a small class.                               *)
Proposition ReplaceSmall : forall (F:ClassRel) (a:U),
  Functional F -> Small F[a].
Proof.
  intros F a H. apply Replacement, H.
Qed.

(* We consider the set defined by the predicate F[a] when F is functional.      *)
Definition replaceSet (F:ClassRel) (a:U) (p:Functional F) : U
  := toSet F[a] (ReplaceSmall F a p).

(* Characterisation of the elements of the replace set of F a.                  *)
Proposition ReplaceCharac : forall (F:ClassRel) (a:U) (p:Functional F),
  forall y, y :< (replaceSet F a p) <-> F[a] y.
Proof.
  unfold replaceSet. intros F a p. apply ClassCharac.
Qed.
