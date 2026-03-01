Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.Fun.
Require Import ZF.Set.Relation.Function.
Require Import ZF.Set.Relation.Functional.
Require Import ZF.Set.Relation.FunctionOn.
Require Import ZF.Set.Relation.Range.
Require Import ZF.Set.Relation.Relation.
Require Import ZF.Set.Single.
Require Import ZF.Set.Union2.

Require Import ZF.Notation.Eval.

(* Extending a function with a single point.                                    *)
Definition extend (f x y:U) : U := f :\/: :{ :(x,y): }:.

Proposition Charac : forall (f x y u:U),
  u :< extend f x y <-> u :< f \/ u = :(x,y):.
Proof.
  intros f x y u. split; intros H1.
  - apply Union2.Charac in H1. destruct H1 as [H1|H1].
    + left. assumption.
    + apply Single.Charac in H1. right. assumption.
  - destruct H1 as [H1|H1]; apply Union2.Charac.
    + left. assumption.
    + right. apply Single.Charac. assumption.
Qed.

Proposition Charac2 : forall (f x y u v:U),
  :(u,v): :< extend f x y <-> :(u,v): :< f \/ u = x /\ v = y.
Proof.
  intros f x y u v. split; intros H1.
  - apply Charac in H1. destruct H1 as [H1|H1].
    + left. assumption.
    + right. apply OrdPair.WhenEqual in H1. assumption.
  - destruct H1 as [H1|[H1 H2]]; apply Charac.
    + left. assumption.
    + right. subst. reflexivity.
Qed.

Proposition IsRelation : forall (f x y:U),
  Relation f -> Relation (extend f x y).
Proof.
  intros f x y H1 u H2. apply Charac in H2. destruct H2 as [H2|H2].
  - apply H1. assumption.
  - exists x, y. assumption.
Qed.

Proposition IsFunctional : forall (f x y:U), ~ x :< domain f ->
  Functional f -> Functional (extend f x y).
Proof.
  intros f x y H1 H2 u y1 y2 H3 H4.
  apply Charac2 in H3. apply Charac2 in H4.
  destruct H3 as [H3|[H3 H5]]; destruct H4 as [H4|[H4 H6]].
  - apply H2 with u; assumption.
  - subst. exfalso. apply H1. apply Domain.Charac. exists y1. assumption.
  - subst. exfalso. apply H1. apply Domain.Charac. exists y2. assumption.
  - subst. reflexivity.
Qed.

Proposition IsFunction : forall (f x y:U), ~ x :< domain f ->
  Function f -> Function (extend f x y).
Proof.
  intros f x y H1 [H2 H3]. split.
  - apply IsRelation. assumption.
  - apply IsFunctional; assumption.
Qed.

Proposition DomainOf : forall (f x y:U),
  domain (extend f x y) = domain f :\/: :{x}:.
Proof.
  intros f x y. apply DoubleInclusion. split; intros u H1.
  - apply Domain.Charac in H1. destruct H1 as [v H1].
    apply Charac2 in H1. destruct H1 as [H1|[H1 H2]]; apply Union2.Charac.
    + left. apply Domain.Charac. exists v. assumption.
    + right. subst. apply Single.Charac. reflexivity.
  - apply Union2.Charac in H1. destruct H1 as [H1|H1]; apply Domain.Charac.
    + apply Domain.Charac in H1. destruct H1 as [v H1]. exists v.
      apply Charac2. left. assumption.
    + apply Single.Charac in H1. subst. exists y.
      apply Charac2. right. split; reflexivity.
Qed.

Proposition IsFunctionOn : forall (f a x y:U), ~ x :< a ->
  FunctionOn f a -> FunctionOn (extend f x y) (a :\/: :{x}:).
Proof.
  intros f a x y H1 [H2 H3]. split; subst.
  - apply IsFunction; assumption.
  - apply DomainOf.
Qed.

Proposition RangeOf : forall (f b x y:U), y :< b ->
  range f :<=: b -> range (extend f x y) :<=: b.
Proof.
  intros f b x y H1 H2 v H3.
  apply Range.Charac in H3. destruct H3 as [u H3].
  apply Charac2 in H3. destruct H3 as [H3|[H3 H4]].
  - apply H2, Range.Charac. exists u. assumption.
  - subst. assumption.
Qed.

Proposition IsFun : forall (f a b x y:U),
  ~ x :< a                             ->
  y :< b                               ->
  Fun f a b                            ->
  Fun (extend f x y) (a :\/: :{x}:) b.
Proof.
  intros f a b x y H1 H2 [H3 H4]. split.
  - apply IsFunctionOn; assumption.
  - apply RangeOf; assumption.
Qed.

Proposition Evalf : forall (f x y u:U),
  ~ x :< domain f           ->
  Functional f              ->
  u :< domain f             ->
  (extend f x y)!u = f!u.
Proof.
  intros f x y u H1 H2 H3. apply Eval.Charac.
  - apply IsFunctional; assumption.
  - rewrite DomainOf. apply Union2.Charac. left. assumption.
  - apply Charac2. left. apply Eval.Satisfies; assumption.
Qed.

Proposition Evalx : forall (f x y:U),
  ~ x :< domain f           ->
  Functional f              ->
  (extend f x y)!x = y.
Proof.
  intros f x y H1 H2. apply Eval.Charac.
  - apply IsFunctional; assumption.
  - rewrite DomainOf. apply Union2.Charac. right.
    apply Single.Charac. reflexivity.
  - apply Charac2. right. split; reflexivity.
Qed.
