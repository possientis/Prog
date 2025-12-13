Require Import ZF.Class.Equiv.
Require Import ZF.Class.Ordinal.Order.Le.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Order.E.
Require Import ZF.Set.Order.RestrictOfClass.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Mult.
Require Import ZF.Set.Ordinal.Plus.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Prod.
Require Import ZF.Set.Relation.Bijection.
Require Import ZF.Set.Relation.BijectionOn.
Require Import ZF.Set.Relation.Converse.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Functional.
Require Import ZF.Set.Relation.OneToOne.
Require Import ZF.Set.Relation.Functional.
Require Import ZF.Set.Relation.Range.
Require Import ZF.Set.Relation.Relation.
Require Import ZF.Set.Specify.

Module SOR := ZF.Set.Order.RestrictOfClass.
Module SPR := ZF.Set.Prod.

(* Lexicographic order on b x a.                                                *)
Definition le (a b:U) : U := Le :/: (b :x: a).

(* The order induced by :< on the ordinal a*b.                                  *)
Definition r (a b:U) : U := E (a :*: b).

(* Helper class to define isomorphism from bxa to a*b.                          *)
Definition F (a b:U) : Class := fun x =>
  exists c d, c :< b /\ d :< a /\ x = :( :(c,d):, a :*: c :+: d):.

(* Our isomorphism candidate.                                                   *)
Definition f (a b:U) : U := {{ x :< (b :x: a) :x: (a :*: b) | F a b }}.

Proposition FCharac2 : forall (a b x y:U),
  F a b :(x,y): <-> exists c d,
    c :< b /\ d :< a /\ x = :(c,d): /\ y = a :*: c :+: d.
Proof.
  intros a b x y. split; intros H1.
  - destruct H1 as [c [d [H1 [H2 H3]]]].
    apply OrdPair.WhenEqual in H3. destruct H3 as [H3 H4].
    exists c. exists d. split. 1: assumption. split. 1: assumption.
    split; assumption.
  - destruct H1 as [c [d [H1 [H2 [H3 H4]]]]]. exists c. exists d. subst.
    split. 1: assumption. split. 1: assumption. reflexivity.
Qed.

Proposition leCharac2 : forall (a b c d c' d':U),
  :( :(c,d):, :(c',d'): ): :< le a b <->
    c  :< b                           /\
    c' :< b                           /\
    d  :< a                           /\
    d' :< a                           /\
    (c :< c' \/ (c = c' /\ d :< d')).
Proof.
  intros a b c d c' d'. split; intros H1.
  - apply SOR.Charac2 in H1. destruct H1 as [H1 [H2 H3]].
    apply SPR.Charac2 in H1. destruct H1 as [H1 H4].
    apply SPR.Charac2 in H2. destruct H2 as [H2 H5].
    apply Le.Charac4 in H3. split. 1: assumption. split. 1: assumption.
    split. 1: assumption. split; assumption.
  - destruct H1 as [H1 [H2 [H3 [H4 H5]]]].
    apply SOR.Charac2. split.
    + apply SPR.Charac2. split; assumption.
    + split.
      * apply SPR.Charac2. split; assumption.
      * apply Le.Charac4. assumption.
Qed.

Lemma Inequality : forall (a b c d:U),
  Ordinal a                   ->
  Ordinal b                   ->
  d :< a                      ->
  c :< b                      ->
  a :*: c :+: d :< a :*: b.
Proof.
  intros a b c d H1 H2 H3 H4.
  assert (Ordinal c) as G1. { apply Core.IsOrdinal with b; assumption. }
  assert (Ordinal d) as G2. { apply Core.IsOrdinal with a; assumption. }
  assert (Ordinal (a :*: b)) as G3. { apply Mult.IsOrdinal; assumption. }
  assert (Ordinal (a :*: c)) as G4. { apply Mult.IsOrdinal; assumption. }
  assert (Ordinal (a :*: c :+: a)) as G5. { apply Plus.IsOrdinal; assumption. }
  assert (Ordinal (a :*: c :+: d)) as G6. { apply Plus.IsOrdinal; assumption. }
  assert (Ordinal (succ c)) as G7. { apply Succ.IsOrdinal. assumption. }
  apply Core.ElemInclTran with (a :*: c :+: a); try assumption.
  - apply Plus.ElemCompatR; assumption.
  - rewrite <- Mult.WhenSuccR. 2: assumption.
    apply Mult.InclCompatR; try assumption.
    apply Succ.ElemIsIncl; assumption.
Qed.

Proposition Charac2 : forall (a b x y:U), Ordinal a -> Ordinal b ->
  :(x,y): :< f a b  <-> exists c d,
    c :< b /\ d :< a /\ x = :(c,d): /\ y = a :*: c :+: d.
Proof.
  intros a b x y H1 H2. split; intros H3.
  - apply Specify.Charac in H3. destruct H3 as [H3 H4].
    apply FCharac2 in H4. assumption.
  - destruct H3 as [c [d [H3 [H4 [H5 H6]]]]].
    apply Specify.Charac. split.
    + apply SPR.Charac2. subst. split.
      * apply SPR.Charac2. split; assumption.
      * apply Inequality; assumption.
    + apply FCharac2. exists c. exists d.
      split. 1: assumption. split. 1: assumption. split; assumption.
Qed.

Proposition IsRelation : forall (a b:U), Relation (f a b).
Proof.
  intros a b x H1.
  apply Specify.Charac in H1. destruct H1 as [H1 _].
  apply SPR.Charac in H1. destruct H1 as [y [z [H1 _]]].
  exists y. exists z. assumption.
Qed.

Proposition IsFunctional  : forall (a b:U), Ordinal a -> Ordinal b ->
  Functional (f a b).
Proof.
  intros a b H1 H2 x y1 y2 H3 H4.
  apply Charac2 in H3; try assumption. apply Charac2 in H4; try assumption.
  destruct H3 as [c [d [H3 [H5 [H6 H7]]]]].
  destruct H4 as [c' [d' [H4 [H8 [H9 H10]]]]]. subst.
  apply OrdPair.WhenEqual in H9. destruct H9 as [H9 H10]. subst. reflexivity.
Qed.

Proposition IsOneToOne : forall (a b:U), Ordinal a -> Ordinal b ->
  OneToOne (f a b).
Proof.
  intros a b H1 H2. split. 1: { apply IsFunctional; assumption. }
  intros y x1 x2 H3 H4.
  apply Converse.Charac2, Charac2 in H3; try assumption.
  apply Converse.Charac2, Charac2 in H4; try assumption.
  destruct H3 as [c [d [H3 [H5 [H6 H7]]]]].
  destruct H4 as [c' [d' [H4 [H8 [H9 H10]]]]].
  assert (Ordinal c)  as G1. { apply Core.IsOrdinal with b; assumption. }
  assert (Ordinal c') as G2. { apply Core.IsOrdinal with b; assumption. }
  assert (Ordinal d)  as G3. { apply Core.IsOrdinal with a; assumption. }
  assert (Ordinal d') as G4. { apply Core.IsOrdinal with a; assumption. }
  subst.
  assert (c = c' /\ d = d') as [H11 H12]. {
    apply Mult.EuclidUnique with a; assumption. }
  subst. reflexivity.
Qed.

Proposition IsBijection : forall (a b:U), Ordinal a -> Ordinal b ->
  Bijection (f a b).
Proof.
  intros a b H1 H2. split.
  - apply IsRelation.
  - apply IsOneToOne; assumption.
Qed.

Proposition DomainOf : forall (a b:U), Ordinal a -> Ordinal b ->
  domain (f a b) = b :x: a.
Proof.
  intros a b H1 H2. apply DoubleInclusion. split; intros x H3.
  - apply Domain.Charac in H3. destruct H3 as [y H3].
    apply Charac2 in H3; try assumption.
    destruct H3 as [c [d [H3 [H4 [H5 _]]]]]. subst.
    apply SPR.Charac2. split; assumption.
  - apply SPR.Charac in H3. destruct H3 as [c [d [H3 [H4 H5]]]]. subst.
    apply Domain.Charac. exists (a :*: c :+: d).
    apply Charac2; try assumption. exists c. exists d.
    split. 1: assumption. split. 1: assumption. split; reflexivity.
Qed.

Proposition IsBijectionOn : forall (a b:U), Ordinal a -> Ordinal b ->
  BijectionOn (f a b) (b :x: a).
Proof.
  intros a b H1 H2. split.
  - apply IsBijection; assumption.
  - apply DomainOf; assumption.
Qed.

Proposition RangeOf : forall (a b:U), Ordinal a -> Ordinal b ->
  range (f a b) = a :*: b.
Proof.
  intros a b H1 H2. apply DoubleInclusion. split; intros y H3.
  - apply Range.Charac in H3. destruct H3 as [x H3].
    apply Charac2 in H3; try assumption.
    destruct H3 as [c [d [H3 [H4 [H5 H6]]]]]. subst.
    apply Inequality; assumption.
  - Admitted.
