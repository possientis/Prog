Require Import ZF.Class.Incl.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Inter2.
Require Import ZF.Set.Core.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Rank.

Module CEM := ZF.Class.Empty.

Proposition Foundation : forall (A:Class),
  A :<>: :0: -> exists a, A a /\ toClass a :/\: A :~: :0:.
Proof.
  intros A H1.
  remember (fun b => exists a, A a /\ b = rank a) as B eqn:H2.
  assert (B :<>: :0:) as H3. {
    apply CEM.HasElem in H1. destruct H1 as [a H1].
    apply CEM.HasElem. exists (rank a). rewrite H2. exists a.
    split. 1: assumption. reflexivity. }
  assert (B :<=: Ordinal) as H4. {
    intros b H4. rewrite H2 in H4. destruct H4 as [a [H4 H5]].
    subst. apply Rank.IsOrdinal. }
  assert (exists b, Ordinal b /\ B b /\ forall c, B c -> b :<=: c) as H6. {
    apply Core.HasMinimal; assumption. }
  destruct H6 as [b [H6 [H7 H8]]]. rewrite H2 in H7. destruct H7 as [a [H7 H9]].
  exists a. split. 1: assumption.
  assert (toClass a :/\: A :~: :0:) as H10. {
    intros c. split; intros H10.
    - exfalso. destruct H10 as [H10 H11].
Admitted.
