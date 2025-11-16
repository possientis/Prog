Require Import ZF.Class.Equiv.
Require Import ZF.Class.Ordinal.Order.Le.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Order.RestrictOfClass.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.Ordinal.Plus.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Prod.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Function.
Require Import ZF.Set.Relation.Functional.
Require Import ZF.Set.Relation.FunctionOn.
Require Import ZF.Set.Relation.Range.
Require Import ZF.Set.Relation.Relation.
Require Import ZF.Set.Single.
Require Import ZF.Set.Specify.
Require Import ZF.Set.Union2.

(* Will be shown to be isomorphic to a + b when endowed with lexic order.       *)
Definition sum (a b:U) : U := :{ :0: }: :x: a :\/: :{ :1: }: :x: b.

(* Lexicographic order on sum a b.                                              *)
Definition le (a b:U) : U := Le :/: (sum a b).

(* Helper class to define isomorphism from sum a b to a + b.                    *)
(* F(0,c) = c     when c :< a                                                   *)
(* F(1,c) = a + c when c :< b                                                   *)
Definition F (a b:U) : Class := fun x =>
  exists c,
    (x = :( :( :0: , c ): , c ):       /\ c :< a) \/
    (x = :( :( :1: , c ): , a :+: c ): /\ c :< b).

(* Our isomorphism candidate.                                                   *)
Definition f (a b:U) : U := :{ x :< (sum a b) :x: (a :+: b) | F a b }:.

Proposition FCharac2 : forall (a b x y:U),
  F a b :(x,y): <-> exists c,
    (c :< a /\ x = :( :0: , c ): /\ y = c)          \/
    (c :< b /\ x = :( :1: , c ): /\ y = a :+: c).
Proof.
  intros a b x y. split; intros H1.
  - destruct H1 as [c [[H1 H2]|[H1 H2]]]; apply OrdPair.WhenEqual in H1;
    destruct H1 as [H1 H3]; exists c.
    + left.  split. 1: assumption. split; assumption.
    + right. split. 1: assumption. split; assumption.
  - destruct H1 as [c [[H1 [H2 H3]]|[H1 [H2 H3]]]]; exists c.
    + left.  split. 2: assumption. subst. reflexivity.
    + right. split. 2: assumption. subst. reflexivity.
Qed.

Proposition Charac2 : forall (a b x y:U), Ordinal a -> Ordinal b ->
  :(x,y): :< f a b <-> exists c,
    (c :< a /\ x = :( :0: , c ): /\ y = c)          \/
    (c :< b /\ x = :( :1: , c ): /\ y = a :+: c).
Proof.
  intros a b x y G1 G2. split; intros H1.
  - apply Specify.Charac in H1. destruct H1 as [H1 H2].
    apply FCharac2 in H2. assumption.
  - destruct H1 as [c [H1|H1]]; apply Specify.Charac.
    + split. 2: { apply FCharac2. exists c. left. assumption. }
      destruct H1 as [H1 [H2 H3]]. apply Prod.Charac2. split.
      * apply Union2.Charac. left. subst. apply Prod.Charac2.
        split. 2: assumption. apply Single.Charac. reflexivity.
      * subst. apply Core.ElemInclTran with a; try assumption.
        { apply Core.IsOrdinal with a; assumption. }
        { apply Plus.IsOrdinal; assumption. }
        { apply Plus.IsInclAddR; assumption. }
    + split. 2: { apply FCharac2. exists c. right. assumption. }
      destruct H1 as [H1 [H2 H3]]. apply Prod.Charac2. split.
      * apply Union2.Charac. right. subst. apply Prod.Charac2.
        split. 2: assumption. apply Single.Charac. reflexivity.
      * subst. apply Plus.ElemCompatR; try assumption.
        apply Core.IsOrdinal with b; assumption.
Qed.

Proposition IsRelation : forall (a b:U), Relation (f a b).
Proof.
  intros a b x H1.
  apply Specify.Charac in H1. destruct H1 as [H1 _].
  apply Prod.Charac in H1. destruct H1 as [y [z [H1 _]]].
  exists y. exists z. assumption.
Qed.

Proposition IsFunctional : forall (a b:U), Ordinal a -> Ordinal b ->
  Functional (f a b).
Proof.
  intros a b H1 H2 x y1 y2 H3 H4.
  apply Charac2 in H3; try assumption. apply Charac2 in H4; try assumption.
  destruct H3 as [c [[H3 [H5 H6]]|[H3 [H5 H6]]]];
  destruct H4 as [d [[H4 [H7 H8]]|[H4 [H7 H8]]]];
  subst; apply OrdPair.WhenEqual in H7.
  - apply H7.
  - destruct H7 as [H7 _]. exfalso. revert H7. apply Natural.ZeroIsNotOne.
  - destruct H7 as [H7 _]. symmetry in H7.
    exfalso. revert H7. apply Natural.ZeroIsNotOne.
  - destruct H7 as [_ H7]. subst. reflexivity.
Qed.

Proposition IsFunction : forall (a b:U), Ordinal a -> Ordinal b ->
  Function (f a b).
Proof.
  intros a b H1 H2. split.
  - apply IsRelation.
  - apply IsFunctional; assumption.
Qed.

Proposition DomainOf : forall (a b:U), Ordinal a -> Ordinal b ->
  domain (f a b) = sum a b.
Proof.
  intros a b H1 H2. apply DoubleInclusion. split; intros x H3.
  - apply Domain.Charac in H3. destruct H3 as [y H3].
    apply Charac2 in H3; try assumption.
    destruct H3 as [c [[H3 [H4 H5]]|[H3 [H4 H5]]]]; apply Union2.Charac.
    + left. subst. apply Prod.Charac2. split. 2: assumption.
      apply Single.Charac. reflexivity.
    + right. subst. apply Prod.Charac2. split. 2: assumption.
      apply Single.Charac. reflexivity.
  - apply Union2.Charac in H3. destruct H3 as [H3|H3];
    apply Prod.Charac in H3; destruct H3 as [y [z [H3 [H4 H5]]]];
    apply Single.Charac in H4; subst; apply Domain.Charac.
    + exists z. apply Charac2; try assumption. exists z. left.
      split. 1: assumption. split; reflexivity.
    + exists (a :+: z). apply Charac2; try assumption. exists z. right.
      split. 1: assumption. split; reflexivity.
Qed.

Proposition IsFunctionOn : forall (a b:U), Ordinal a -> Ordinal b ->
  FunctionOn (f a b) (sum a b).
Proof.
  intros a b H1 H2. split.
  - apply IsFunction; assumption.
  - apply DomainOf; assumption.
Qed.

Proposition RangeOf : forall (a b:U), Ordinal a -> Ordinal b ->
  range (f a b) = a :+: b.
Proof.
  intros a b H1 H2. apply DoubleInclusion. split; intros y H3.
  - apply Range.Charac in H3. destruct H3 as [x H3].
    apply Charac2 in H3; try assumption.
    destruct H3 as [c [[H3 [H4 H5]]|[H3 [H4 H5]]]]; subst.
    + apply Core.ElemInclTran with a; try assumption.
      * apply Core.IsOrdinal with a; assumption.
      * apply Plus.IsOrdinal; assumption.
      * apply Plus.IsInclAddR; assumption.
    + apply Plus.ElemCompatR; try assumption.
      apply Core.IsOrdinal with b; assumption.
  - assert (Ordinal (a :+: b)) as H6. { apply Plus.IsOrdinal; assumption. }
    assert (Ordinal y) as H7. {
      apply Core.IsOrdinal with (a :+: b); assumption. }
    assert (y :< a \/ a :<=: y ) as H8. { apply Core.ElemOrIncl; assumption. }
    destruct H8 as [H8|H8]; apply Range.Charac.
    + exists :(:0:,y):. apply Charac2; try assumption. exists y. left.
      split. 1: assumption. split; reflexivity.
    + assert (exists c, Ordinal c /\ a :+: c = y) as H9. {
        apply Plus.CompleteR; assumption. }
      destruct H9 as [c [H9 H10]].
      exists :(:1:,c):. apply Charac2; try assumption. exists c. right.
Admitted.
