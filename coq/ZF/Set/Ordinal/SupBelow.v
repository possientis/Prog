Require Import ZF.Class.Equiv.
Require Import ZF.Class.Ordinal.SupBelow.
Require Import ZF.Set.Core.
Require Import ZF.Set.Inter2.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Specify.
Require Import ZF.Set.Union.

Export ZF.Notation.SupBelow.

(* The supremum of the set a below b.                                           *)
Definition supBelow (b a:U) : U := :U( :{ x :< a :/\: b | Ordinal }: ).

(* Notation "sup(:< b ) a" := (supBelow b a)                                    *)
Global Instance SetSupBelow : SupBelow U := { supBelow := supBelow }.

Proposition Charac : forall (a b:U),
  forall x, x :< sup(:<b) a <->
    exists y, x :< y /\ y :< a /\ y :< b /\ Ordinal y.
Proof.
  intros a b x. split; intros H1.
  - apply Union.Charac in H1. destruct H1 as [y [H1 H2]].
    apply Specify.Charac in H2. destruct H2 as [H2 H3].
    apply Inter2.Charac in H2. destruct H2 as [H2 H4].
    exists y. split. 1: assumption. split. 1: assumption.
    split; assumption.
  - destruct H1 as [y [H1 [H2 [H3 H4]]]]. apply Union.Charac.
    exists y. split. 1: assumption. apply Specify.Charac.
    split. 2: assumption. apply Inter2.Charac. split; assumption.
Qed.

(* The supremum below b of the class is the class of the supremum below b.      *)
Proposition ToClass : forall (a b:U),
  sup(:< b) (toClass a) :~: toClass (sup(:< b) a).
Proof.
  intros a b x. split; intros H1.
  - destruct H1 as [y [H1 [H2 [H3 H4]]]]. apply Charac.
    exists y. split. 1: assumption. split. 1: assumption. split; assumption.
  - apply Charac in H1. destruct H1 as [y [H1 [H2 [H3 H4]]]].
    exists y. split. 1: assumption. split. 1: assumption. split; assumption.
Qed.

(* When dealing with ordinals, the supremum of a below b is the union of a/\b.  *)
Proposition WhenOrdinal : forall (a b:U), Ordinal a -> Ordinal b ->
  sup(:< b) a = :U(a :/\: b).
Proof.
  intros a b H1 H2.
  unfold Notation.SupBelow.supBelow, SetSupBelow, supBelow.
  assert (:{ x :< a :/\: b | Ordinal }: = a :/\: b) as H3. {
    apply Specify.IsA. intros x H3. apply Inter2.Charac in H3.
    destruct H3 as [H3 _]. apply Core.IsOrdinal with a; assumption. }
  rewrite H3. reflexivity.
Qed.

(* If b belongs to a, the supremum of a below succ b is b.                      *)
Proposition WhenElem : forall (a b:U), Ordinal a -> Ordinal b ->
  b :< a -> sup(:< succ b) a = b.
Proof.
  intros a b H1 H2 H3.
  assert (a :/\: succ b = succ b) as H4. {
    apply ElemIsIncl in H3; try assumption.
    apply ZF.Set.Incl.DoubleInclusion. split; intros x H4.
    - apply Inter2.Charac in H4. destruct H4 as [_ H4]. assumption.
    - apply Inter2.Charac. split. 2: assumption. apply H3. assumption. }
  rewrite WhenOrdinal. 2: assumption.
  - rewrite H4. apply UnionOfSucc. assumption.
  - apply Succ.IsOrdinal. assumption.
Qed.


