Require Import ZF.Set.Core.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Single.

Definition Decreasing (f:U) : Prop := forall (x y:U),
  x   :< domain f ->
  y   :< domain f ->
  x   :< y        ->
  f!y :< f!x.

Proposition WhenSingle : forall (x y f:U),
  f = :{ :(x,y): }: -> Decreasing f.
Proof.
  intros x y f H1 u v H2 H3 H4. exfalso.
  rewrite Domain.WhenSingle with x y f in H2. 2: assumption.
  rewrite Domain.WhenSingle with x y f in H3. 2: assumption.
  apply Single.Charac in H2. apply Single.Charac in H3. subst.
  revert H4. apply NoElemLoop1.
Qed.
