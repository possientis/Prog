Require Import ZF.Axiom.Replacement.
Require Import ZF.Binary.
Require Import ZF.Binary.Functional.
Require Import ZF.Binary.Image.
Require Import ZF.Class.
Require Import ZF.Class.Small.
Require Import ZF.Set.

(* It is useful to define the predicate underlying the replacement axiom.       *)
Definition ReplacePred (F:Binary) (a:U) : U -> Prop := fun y =>
  exists x, x :< a /\ F x y.

(* This predicate is exactly F[a], the direct image of a by F.                  *)
Proposition ReplacePredImage : forall (F:Binary) (a:U) (y:U),
    ReplacePred F a y <-> F:[toClass a]: y.
Proof.
  intros F a y. split; auto.
Qed.

(* If F is functional then F[toClass a] is a small class.                       *)
Proposition ReplaceSmall : forall (F:Binary) (a:U),
  Functional F -> Small F:[toClass a]:.
Proof.
  intros F a H. apply Replacement, H.
Qed.

(* We consider the set defined by the predicate F[a] when F is functional.      *)
Definition replaceSet (F:Binary) (a:U) (p:Functional F) : U
  := toSet F:[toClass a]: (ReplaceSmall F a p).

(* Characterisation of the elements of the replace set of F a.                  *)
Proposition ReplaceCharac : forall (F:Binary) (a:U) (p:Functional F),
  forall y, y :< (replaceSet F a p) <-> F:[toClass a]: y.
Proof.
  unfold replaceSet. intros F a p. apply ClassCharac.
Qed.
