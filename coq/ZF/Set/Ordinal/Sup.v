Require Import ZF.Class.Core.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Ordinal.Sup.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Inter2.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Limit.
Require Import ZF.Set.Ordinal.NonLimit.
Require Import ZF.Set.Ordinal.Omega.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Specify.
Require Import ZF.Set.Union.

Export ZF.Notation.SupBelow.

(* The supremum of the set a.                                                   *)
Definition sup (a:U) : U := :U( :{ a | Ordinal }: ).


(* The supremum of the set a below b.                                           *)
Definition supBelow (b a:U) : U := :U( :{ a :/\: b | Ordinal }: ).

(* Notation "sup(:< b ) a" := (supBelow b a)                                    *)
Global Instance SetSupBelow : SupBelow U := { supBelow := supBelow }.

Proposition Charac : forall (a:U),
  forall x, x :< sup a <-> exists y, x :< y /\ y :< a /\ Ordinal y.
Proof.
  intros a x. split; intros H1.
  - apply Union.Charac in H1. destruct H1 as [y [H1 H2]].
    apply Specify.Charac in H2. destruct H2 as [H2 H3].
    exists y. split. 1: assumption. split; assumption.
  - destruct H1 as [y [H1 [H2 H3]]]. apply Union.Charac.
    exists y. split. 1: assumption. apply Specify.Charac.
    split; assumption.
Qed.

Proposition CharacBelow : forall (b a:U),
  forall x, x :< sup(:<b) a <->
    exists y, x :< y /\ y :< a /\ y :< b /\ Ordinal y.
Proof.
  intros b a x. split; intros H1.
  - apply Union.Charac in H1. destruct H1 as [y [H1 H2]].
    apply Specify.Charac in H2. destruct H2 as [H2 H3].
    apply Inter2.Charac in H2. destruct H2 as [H2 H4].
    exists y. split. 1: assumption. split. 1: assumption.
    split; assumption.
  - destruct H1 as [y [H1 [H2 [H3 H4]]]]. apply Union.Charac.
    exists y. split. 1: assumption. apply Specify.Charac.
    split. 2: assumption. apply Inter2.Charac. split; assumption.
Qed.

(* The supremum of the class is the class of the supremum.                      *)
Proposition ToClass : forall (a:U),
  Class.Ordinal.Sup.sup (toClass a) :~: toClass (sup a).
Proof.
  intros a x. split; intros H1.
  - destruct H1 as [y [H1 [H2 H3]]]. apply Charac. exists y.
    split. 1: assumption. split; assumption.
  - apply Charac in H1. destruct H1 as [y [H1 [H2 H3]]].
    exists y. split. 1: assumption. split; assumption.
Qed.

(* The supremum below b of the class is the class of the supremum below b.      *)
Proposition ToClassBelow : forall (a b:U),
  sup(:< b) (toClass a) :~: toClass (sup(:< b) a).
Proof.
  intros a b x. split; intros H1.
  - destruct H1 as [y [H1 [H2 [H3 H4]]]]. apply CharacBelow.
    exists y. split. 1: assumption. split. 1: assumption. split; assumption.
  - apply CharacBelow in H1. destruct H1 as [y [H1 [H2 [H3 H4]]]].
    exists y. split. 1: assumption. split. 1: assumption. split; assumption.
Qed.

(* The supremum of an ordinal is simply its union.                              *)
Proposition WhenOrdinal : forall (a:U),
  Ordinal a -> sup a = :U(a).
Proof.
  intros a H1. unfold sup.
  assert (:{a | Ordinal}: = a) as H2. {
    apply Specify.IsA. intros x H2. apply Core.IsOrdinal with a; assumption. }
  rewrite H2. reflexivity.
Qed.

(* When dealing with ordinals, the supremum of a below b is the union of a/\b.  *)
Proposition WhenOrdinalBelow : forall (a b:U), Ordinal a -> Ordinal b ->
  sup(:< b) a = :U(a :/\: b).
Proof.
  intros a b H1 H2.
  unfold Notation.SupBelow.supBelow, SetSupBelow, supBelow.
  assert (:{a :/\: b | Ordinal}: = a :/\: b) as H3. {
    apply Specify.IsA. intros x H3. apply Inter2.Charac in H3.
    destruct H3 as [H3 _]. apply Core.IsOrdinal with a; assumption. }
  rewrite H3. reflexivity.
Qed.

(* The supremum of an ordinal is an ordinal.                                    *)
Proposition IsOrdinal : forall (a:U), Ordinal a ->
  Ordinal (sup a).
Proof.
  intros a H1. rewrite WhenOrdinal. 2: assumption.
  apply UnionOf.IsOrdinal. assumption.
Qed.

(* The supremum of the successor of an ordinal is the ordinal.                  *)
Proposition WhenSucc : forall (a:U), Ordinal a ->
  sup (succ a) = a.
Proof.
  intros a H1. rewrite WhenOrdinal.
  - apply UnionOfSucc. assumption.
  - apply Succ.IsOrdinal. assumption.
Qed.

(* The supremum of a limit ordinal is itself.                                   *)
Proposition WhenLimit : forall (a:U),
  Limit a -> sup a = a.
Proof.
  intros a H1.
  assert (Ordinal a) as H2. { apply Limit.HasOrdinalElem. assumption. }
  rewrite WhenOrdinal. 2: assumption. symmetry. apply Limit.Charac in H1.
  2: assumption. destruct H1 as [_ H1]. assumption.
Qed.

(* The supremum of N is N itself.                                               *)
Proposition WhenOmega : sup :N = :N.
Proof.
  apply WhenLimit. apply Omega.IsLimit.
Qed.

(* A non-empty, non-limit ordinal is equal to the successor of its supremum.    *)
Proposition WhenNonLimit : forall (a:U),
  NonLimit a -> a <> :0: -> a = succ (sup a).
Proof.
  intros a H1 H2.
  assert (Ordinal a) as H3. { apply NonLimit.HasOrdinalElem. assumption. }
  rewrite WhenOrdinal. 2: assumption.
  apply NonLimit.Charac in H1. 2: assumption.
  destruct H1 as [H1|H1]. 2: assumption. contradiction.
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
  rewrite WhenOrdinalBelow. 2: assumption.
  - rewrite H4. apply UnionOfSucc. assumption.
  - apply Succ.IsOrdinal. assumption.
Qed.

(* The supremum of an ordinal is an upper-bound of its elements.                *)
Proposition IsUpperBound : forall (a b:U), Ordinal a ->
  b :< a -> b :<=: sup a.
Proof.
  intros a b H1 H2. rewrite WhenOrdinal. 2: assumption.
  apply UnionOf.IsUpperBound; assumption.
Qed.

(* The supremum of an ordinal is the smallest upper-bound.                      *)
Proposition IsSmallest : forall (a b:U),
  Ordinal a                       ->
  Ordinal b                       ->
  (forall c, c :< a -> c :<=: b)  ->
  sup a :<=: b.
Proof.
  intros a b H1 H2. rewrite WhenOrdinal. 2: assumption.
  apply UnionOf.IsSmallest; assumption.
Qed.

(* The supremum of an ordinal is not an element of it iff it is equal to it.    *)
Proposition NotElemIsEqual : forall (a:U), Ordinal a ->
  ~ sup a :< a <-> sup a = a.
Proof.
  intros a H1. rewrite WhenOrdinal. 2: assumption.
  apply UnionOf.NotElemIsEqual. assumption.
Qed.

(* The supremum of an ordinal is a subset of it.                                *)
Proposition IsIncl : forall (a:U), Ordinal a ->
  sup a :<=: a.
Proof.
  intros a H1. rewrite WhenOrdinal. 2: assumption.
  apply UnionOf.IsIncl. assumption.
Qed.
