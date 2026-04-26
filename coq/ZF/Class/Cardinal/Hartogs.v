Require Import ZF.Class.Equiv.
Require Import ZF.Class.Small.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Class.Relation.Relation.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Order.E.
Require Import ZF.Set.Order.Isom.
Require Import ZF.Set.Order.WellOrdering.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Inj.

Definition hartogs (a:U) : Class := fun b =>
  Ordinal b /\ exists f, Inj f b a.

Definition isom : Class := fun y => exists r x f, y = :(:(r,x):,f):   /\
  ((~WellOrdering r x /\ f = :0:)                                     \/
   ( WellOrdering r x /\ exists b, Ordinal b /\ Isom f r (E b) x b)).

Proposition Charac2 : forall (r x f:U),
  isom :(:(r,x):,f): <->
  (~WellOrdering r x /\ f = :0:)                                     \/
  ( WellOrdering r x /\ exists b, Ordinal b /\ Isom f r (E b) x b).
Proof.
  (* Proof by Claude.                                                           *)
  (* Direct unfolding of isom: membership reduces to the two-case disjunction.  *)
  (* OrdPair injectivity forces r'=r, x'=x, f'=f, collapsing the existentials.  *)
  intros r x f. unfold isom. split.
  - intros [r' [x' [f' [H1 H2]]]].
    apply OrdPair.WhenEqual in H1. destruct H1 as [H1 H3].
    apply OrdPair.WhenEqual in H1. destruct H1 as [H1 H4].
    subst. assumption.
  - intros H1. exists r, x, f. split. reflexivity. assumption.
Qed.

Proposition IsRelation : Relation isom.
Proof.
Admitted.

Proposition IsFunctional : Functional isom.
Proof.
Admitted.
