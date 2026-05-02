Require Import ZF.Class.Equiv.
Require Import ZF.Class.Order.Transport.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Bij.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.Functional.
Require Import ZF.Set.Truncate.

Module CIN := ZF.Class.Incl.
Module COT := ZF.Class.Order.Transport.

Definition transport (f r a:U) : U :=
  truncate (COT.transport (toClass f) (toClass r) (toClass a)).

Proposition ToClass : forall (f r a:U),
  Functional f                                      ->
  a :<=: domain f                                   ->
  toClass (transport f r a) :~:
  COT.transport (toClass f) (toClass r) (toClass a).
Proof.
  intros f r a H1 H2.
  apply Truncate.WhenSmall, COT.IsSmall. 1: assumption.
  - apply CIN.EquivCompatR with (toClass (domain f)). 2: assumption.
    apply Domain.ToClass.
  - apply Small.SetIsSmall.
Qed.

Proposition Charac : forall (f r a x:U),
  Functional f                                      ->
  a :<=: domain f                                   ->
  x :< transport f r a                             <->
  exists y z,
    x = :(f!y,f!z):   /\
    y :< a            /\
    z :< a            /\
    :(y,z): :< r.
Proof.
  intros f r a x H1 H2. split; intros H3.
  - apply ToClass in H3; assumption.
  - apply ToClass; assumption.
Qed.

Proposition Charac2f : forall (f r a b y z:U),
  Bij f a b                                         ->
  y :< a                                            ->
  z :< a                                            ->
  :(f!y,f!z): :< transport f r a <-> :(y,z): :< r.
Proof.
  intros f r a b y z H1 H2 H3.
  assert (Functional f) as G1. { apply H1. }
  assert (domain f = a) as G2. { apply H1. }
  assert (a :<=: domain f) as G3. { rewrite G2. apply Incl.Refl. }
  split; intros H4.
  - apply Charac in H4; try assumption.
    destruct H4 as [y' [z' [H4 [H5 [H6 H7]]]]].
    apply OrdPair.WhenEqual in H4. destruct H4 as [H4 H8].
    assert (y = y') as H9.   { apply Bij.EvalInjective with f a b; assumption. }
    assert (z = z') as H910. { apply Bij.EvalInjective with f a b; assumption. }
    subst. assumption.
  - apply Charac; try assumption. exists y, z. split. 1: reflexivity.
    split. 1: assumption. split; assumption.
Qed.
