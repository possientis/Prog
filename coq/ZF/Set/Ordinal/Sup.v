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

Proposition ToClass : forall (a:U),
  Class.Ordinal.Sup.sup (toClass a) :~: toClass (sup a).
Proof.
  intros a x. split; intros H1.
  - destruct H1 as [y [H1 [H2 H3]]]. apply Charac. exists y.
    split. 1: assumption. split; assumption.
  - apply Charac in H1. destruct H1 as [y [H1 [H2 H3]]].
    exists y. split. 1: assumption. split; assumption.
Qed.

Proposition ToClassBelow : forall (a b:U),
  sup(:< b) (toClass a) :~: toClass (sup(:< b) a).
Proof.
  intros a b x. split; intros H1.
  - destruct H1 as [y [H1 [H2 [H3 H4]]]]. apply CharacBelow.
    exists y. split. 1: assumption. split. 1: assumption. split; assumption.
  - apply CharacBelow in H1. destruct H1 as [y [H1 [H2 [H3 H4]]]].
    exists y. split. 1: assumption. split. 1: assumption. split; assumption.
Qed.

Proposition WhenSucc : forall (a:U), Ordinal a ->
  sup (succ a) = a.
Proof.
  intros a H1. unfold sup.
  assert (:{succ a | Ordinal}: = succ a) as H2. {
    apply Specify.IsA. intros x H2. apply Core.IsOrdinal with (succ a).
    2: assumption. apply Succ.IsOrdinal. assumption. }
  rewrite H2. apply UnionOfSucc. assumption.
Qed.

Proposition WhenLimit : forall (a:U),
  Limit a -> sup a = a.
Proof.
  intros a H1.
  assert (Ordinal a) as H2. { apply Limit.HasOrdinalElem. assumption. }
  assert (:{a | Ordinal}: = a) as H3. {
    apply Specify.IsA. intros x H3. apply Core.IsOrdinal with a; assumption. }
  unfold sup. rewrite H3. apply Limit.Charac in H1. 2: assumption.
  symmetry. apply H1.
Qed.

Proposition WhenOmega : sup :N = :N.
Proof.
  apply WhenLimit. apply Omega.IsLimit.
Qed.

Proposition WhenNonLimit : forall (a:U),
  NonLimit a -> a <> :0: -> a = succ (sup a).
Proof.
  intros a H1 H2.
  assert (Ordinal a) as H3. { apply NonLimit.HasOrdinalElem. assumption. }
  assert (:{a | Ordinal}: = a) as H4. {
    apply Specify.IsA. intros x H4. apply Core.IsOrdinal with a; assumption. }
  unfold sup. rewrite H4. apply NonLimit.Charac in H1. 2: assumption.
  destruct H1 as [H1|H1]. 2: assumption. - contradiction.
Qed.
