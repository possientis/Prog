Require Import ZF.Class.Equiv.
Require Import ZF.Class.Order.E.
Require Import ZF.Class.Ordinal.Order.Le.
Require Import ZF.Set.Core.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Order.Isom.
Require Import ZF.Set.Order.RestrictOfClass.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.Ordinal.Plus.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Prod.
Require Import ZF.Set.Relation.Bij.
Require Import ZF.Set.Relation.Bijection.
Require Import ZF.Set.Relation.BijectionOn.
Require Import ZF.Set.Relation.Converse.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.Functional.
Require Import ZF.Set.Relation.OneToOne.
Require Import ZF.Set.Relation.Range.
Require Import ZF.Set.Relation.Relation.
Require Import ZF.Set.Single.
Require Import ZF.Set.Specify.
Require Import ZF.Set.Union2.

Require Import ZF.Notation.Eval. (* TODO: already exported by Eval so why ? *)

Module COR := ZF.Set.Order.RestrictOfClass.

(* Will be shown to be isomorphic to a + b when endowed with lexic order.       *)
Definition sum (a b:U) : U := :{ :0: }: :x: a :\/: :{ :1: }: :x: b.

(* Lexicographic order on sum a b.                                              *)
Definition le (a b:U) : U := Le :/: (sum a b).

(* The order induced by :< on the ordinal a + b.                                *)
Definition r (a b:U) : U := E :/: (a :+: b).

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

Proposition IsOneToOne : forall (a b:U), Ordinal a -> Ordinal b ->
  OneToOne (f a b).
Proof.
  intros a b H1 H2. split. 1: { apply IsFunctional; assumption. }
  intros y x1 x2 H3 H4.
  apply Converse.Charac2, Charac2 in H3; try assumption.
  apply Converse.Charac2, Charac2 in H4; try assumption.
  destruct H3 as [c [[H3 [H5 H6]]|[H3 [H5 H6]]]];
  destruct H4 as [d [[H4 [H7 H8]]|[H4 [H7 H8]]]];
  subst.
  - reflexivity.
  - exfalso.
    assert (a :< a) as H9. {
      assert (Ordinal d) as H9. { apply Core.IsOrdinal with b; assumption. }
      apply Core.InclElemTran with (a :+: d); try assumption.
      - apply Plus.IsOrdinal; assumption.
      - apply Plus.IsInclAddR; assumption. }
    revert H9. apply NoElemLoop1.
  - exfalso.
    assert (a :< a) as H9. {
      assert (Ordinal c) as H9. { apply Core.IsOrdinal with b; assumption. }
      apply Core.InclElemTran with (a :+: c); try assumption.
      - apply Plus.IsOrdinal; assumption.
      - apply Plus.IsInclAddR; assumption. }
    revert H9. apply NoElemLoop1.
  - assert (Ordinal c) as H9.  { apply Core.IsOrdinal with b; assumption. }
    assert (Ordinal d) as H10. { apply Core.IsOrdinal with b; assumption. }
    apply Plus.CancelL in H8; try assumption. subst. reflexivity.
Qed.

Proposition IsBijection : forall (a b:U), Ordinal a -> Ordinal b ->
  Bijection (f a b).
Proof.
  intros a b H1 H2. split.
  - apply IsRelation.
  - apply IsOneToOne; assumption.
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

Proposition IsBijectionOn : forall (a b:U), Ordinal a -> Ordinal b ->
  BijectionOn (f a b) (sum a b).
Proof.
  intros a b H1 H2. split.
  - apply IsBijection; assumption.
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
      split; subst.
      * apply Plus.ElemCompatRevR with a; assumption.
      * split; reflexivity.
Qed.

(* f a b is a bijection from sum a b to a + b.                                  *)
Proposition IsBij : forall (a b:U), Ordinal a -> Ordinal b ->
  Bij (f a b) (sum a b) (a :+: b).
Proof.
  intros a b H1 H2. split.
  - apply IsBijectionOn; assumption.
  - apply RangeOf; assumption.
Qed.


Proposition Eval0 : forall (a b c:U), Ordinal a -> Ordinal b ->
  c :< a -> (f a b)!(:(:0:,c):) = c.
Proof.
  intros a b c H1 H2 H3. apply Eval.Charac.
  - apply IsFunctional; assumption.
  - rewrite DomainOf; try assumption. apply Union2.Charac. left.
    apply Prod.Charac2. split. 2: assumption. apply Single.Charac. reflexivity.
  - apply Charac2; try assumption. exists c. left.
    split. 1: assumption. split; reflexivity.
Qed.

Proposition Eval1 : forall (a b c:U), Ordinal a -> Ordinal b ->
  c :< b -> (f a b)!(:(:1:,c):) = a :+: c.
Proof.
  intros a b c H1 H2 H3. apply Eval.Charac.
  - apply IsFunctional; assumption.
  - rewrite DomainOf; try assumption. apply Union2.Charac. right.
    apply Prod.Charac2. split. 2: assumption. apply Single.Charac. reflexivity.
  - apply Charac2; try assumption. exists c. right.
    split. 1: assumption. split; reflexivity.
Qed.

(* f a b is an order isomorphism from sum a b to a + b.                         *)
Proposition IsIsom : forall (a b:U), Ordinal a -> Ordinal b ->
  Isom (f a b) (le a b) (r a b) (sum a b) (a :+: b).
Proof.
  intros a b H1 H2. split. 1: { apply IsBij; assumption. }
  intros x y H3 H4. apply Union2.Charac in H3. apply Union2.Charac in H4.
  destruct H3 as [H3|H3]; destruct H4 as [H4|H4];
  apply Prod.Charac in H3; apply Prod.Charac in H4;
  destruct H3 as [x1 [c [H3 [H5 H6]]]]; apply Single.Charac in H5;
  destruct H4 as [x2 [d [H4 [H7 H8]]]]; apply Single.Charac in H7;
  subst; split; intros H9.
  - rewrite Eval0, Eval0; try assumption.
Admitted.
