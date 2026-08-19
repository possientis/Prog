Require Import ZF.Class.Equiv.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.Functional.
Require Import ZF.Set.Relation.FunctionOn.
Require Import ZF.Set.Relation.Image.
Require Import ZF.Set.Union.
Require Import ZF.Set.UnionGenOfClass.

Require Import ZF.Notation.UnionGen.
Export ZF.Notation.UnionGen.


(* The generalized union \/_{x :< a} b(x)                                       *)
Definition unionGen (a b:U) : U := :\/:_{a} (toClass b).

(* Notation ":\/:_{ a } b" := (unionGen a b)                                    *)
Global Instance SetUnionGen : UnionGen U U := { unionGen := unionGen }.

(* y belongs to the generalized union iff y belongs to some b(x) with x in a.   *)
Proposition Charac : forall (a b y:U),
  y :< :\/:_{a} b <-> exists x, x :< a /\ y :< b!x.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a b. apply UnionGenOfClass.Charac.
Qed.

(* The generalized union is the same when the functions b and c agree on a.     *)
Proposition Equal : forall (a b c:U),
  (forall x, x :< a -> b!x = c!x) -> :\/:_{a} b = :\/:_{a} c.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a b c. apply UnionGenOfClass.Equal.
Qed.

(* If x is in a, then b(x) is included in the generalized union over a.         *)
Proposition IsIncl : forall (a b x:U),
  x :< a -> b!x :<=: :\/:_{a} b.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a b. apply UnionGenOfClass.IsIncl.
Qed.

(* The generalized union is monotone in both the index set and the family.      *)
Proposition InclCompat : forall (a b c d:U),
  a :<=: c                            ->
  (forall x, x :< a -> b!x :<=: d!x)  ->
  :\/:_{a} b  :<=: :\/:_{c} d.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a b c d. apply UnionGenOfClass.InclCompat.
Qed.

(* The generalized union is monotone in the left index set.                     *)
Proposition InclCompatL : forall (a b c:U),
  a :<=: c -> :\/:_{a} b :<=: :\/:_{c} b.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a b c. apply UnionGenOfClass.InclCompatL.
Qed.

(* The generalized union is monotone in the right family.                       *)
Proposition InclCompatR : forall (a b c:U),
  (forall x, x :< a -> b!x :<=: c!x)  -> :\/:_{a} b :<=: :\/:_{a} c.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a b c. apply UnionGenOfClass.InclCompatR.
Qed.

(* If each b(x) is a subset of c for x in a, the generalized union is too.      *)
Proposition WhenBounded : forall (a b c:U),
  (forall x, x :< a -> b!x :<=: c) -> :\/:_{a} b :<=: c.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a b c. apply UnionGenOfClass.WhenSetBounded.
Qed.

(* The generalized union over a function equals the union of its image.         *)
Proposition WhenImage : forall (a f:U),
  FunctionOn f a -> :\/:_{a} f = :U(f:[a]:).
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a f H1. transitivity (:U((toClass f):[a]:)).
  - apply UnionGenOfClass.WhenClassImage. apply Functional.ToClass. apply H1.
  - rewrite <- Image.ByClass. reflexivity.
Qed.

