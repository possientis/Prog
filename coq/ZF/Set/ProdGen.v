Require Import ZF.Axiom.Choice.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Relation.Fun.From.
Require Import ZF.Set.Core.
Require Import ZF.Set.Diff.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.FunctionOn.
Require Import ZF.Set.Relation.Map.
Require Import ZF.Set.Relation.Restrict.
Require Import ZF.Set.Single.
Require Import ZF.Set.ProdGenOfClass.
Require Import ZF.Set.UnionGen.

Require Import ZF.Notation.ProdGen.
Export ZF.Notation.ProdGen.


(* The generalized product prd_{x :< a} b(x).                                   *)
Definition prodGen (a b:U) : U := :prd:_{a} (toClass b).

(* Notation ":prd:_{ a } b" := (prodGen a b)                                    *)
Global Instance SetProdGen : ProdGen U U := { prodGen := prodGen }.

(* A set belongs to the product iff it is a function choosing from each fibre.  *)
Proposition Charac : forall (a b f:U),
  f :< :prd:_{a} b <-> FunctionOn f a /\ forall x, x :< a -> f!x :< b!x.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a b. apply ProdGenOfClass.Charac.
Qed.

(* Every member of a product is a function on the index set.                    *)
Proposition IsFunctionOn : forall (a b f:U),
  f :< :prd:_{a} b -> FunctionOn f a.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a b. apply ProdGenOfClass.IsFunctionOn.
Qed.

(* Each value of a product member lies in the corresponding fibre.              *)
Proposition EvalIsIn : forall (a b f x:U),
  f :< :prd:_{a} b -> x :< a -> f!x :< b!x.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a b. apply ProdGenOfClass.EvalIsIn.
Qed.

(* A function choosing from each fibre belongs to the product.                  *)
Proposition IsIn : forall (a b f:U),
  FunctionOn f a                    ->
  (forall x, x :< a -> f!x :< b!x)  ->
  f :< :prd:_{a} b.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a b. apply ProdGenOfClass.IsIn.
Qed.

(* Choice gives a member of a product of non-empty fibres.                      *)
Proposition HasElem : forall (a b:U),
  Choice                              ->
  (forall x, x :< a -> b!x <> :0:)    ->
  exists f, f :< :prd:_{a} b.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a b. apply ProdGenOfClass.HasElem.
Qed.

(* The product is the same when the functions b and c agree on a.               *)
Proposition Equal : forall (a b c:U),
  (forall x, x :< a -> b!x = c!x) -> :prd:_{a} b = :prd:_{a} c.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a b c. apply ProdGenOfClass.Equal.
Qed.

(* Shrinking indices and enlarging fibres preserves product membership.         *)
Proposition InclCompat : forall (a b c d f:U),
  a :<=: c                              ->
  (forall x, x :< a -> b!x :<=: d!x)    ->
  f     :< :prd:_{c} b                  ->
  f:|:a :< :prd:_{a} d.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a b c d f H1 H2 H3.
  apply ProdGenOfClass.InclCompat with (toClass b) c; assumption.
Qed.

(* Restricting a product member to a smaller index set preserves membership.    *)
Proposition InclCompatL : forall (a b c f:U),
  a :<=: c -> f :< :prd:_{c} b -> f:|:a :< :prd:_{a} b.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a b c. apply ProdGenOfClass.InclCompatL.
Qed.

(* Enlarging each fibre enlarges the product over the same index set.           *)
Proposition InclCompatR : forall (a b c:U),
  (forall x, x :< a -> b!x :<=: c!x) -> :prd:_{a} b :<=: :prd:_{a} c.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a b c. apply ProdGenOfClass.InclCompatR.
Qed.

(* A product of fibrewise differences is contained in the original product.     *)
Proposition WhenDiff : forall (a b c:U),
  :prd:_{a} (:[fun x => b!x :\: c!x]:) :<=: :prd:_{a} b.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a b c. apply ProdGenOfClass.WhenDiff.
Qed.

(* If all fibres are contained in c, then the product lies in map(a,c).         *)
Proposition WhenBounded : forall (a b c:U),
  (forall x, x :< a -> b!x :<=: c) -> :prd:_{a} b :<=: map a c.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a b c. apply ProdGenOfClass.WhenBounded.
Qed.

(* The product lies in the map set into the generalized union of its fibres.    *)
Proposition IsIncl : forall (a b:U),
  :prd:_{a} b :<=: map a (:\/:_{a} b).
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a b. apply ProdGenOfClass.IsIncl.
Qed.

(* A product over a constant family is the ordinary map set.                    *)
Proposition WhenConstant : forall (a b c:U),
  (forall x, x :< a -> b!x = c) -> :prd:_{a} b = map a c.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a b c. apply ProdGenOfClass.WhenConstant.
Qed.

(* The product over the empty index set is the singleton empty function.        *)
Proposition WhenZeroL : forall (b:U), :prd:_{:0:} b = :{:0:}:.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros b. apply ProdGenOfClass.WhenZeroL.
Qed.

(* A product is empty when one of its fibres over the index set is empty.       *)
Proposition WhenZeroR : forall (a b x:U),
  x :< a -> b!x = :0: -> :prd:_{a} b = :0:.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a b x H1 H2. apply ProdGenOfClass.WhenZeroR with x; assumption.
Qed.
