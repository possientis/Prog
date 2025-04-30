Require Import ZF.Axiom.Classic.
Require Import ZF.Axiom.Foundation.
Require Import ZF.Class.Core.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Inter2.

(* A non-empty small class A has an element with empty intersection with A.     *)
Proposition Foundation : forall (A:Class),
  A :<>: :0:  ->
  Small A     ->
  exists a, A a /\ toClass a :/\: A :~: :0:.
Proof.
  intros A H1 H2. apply Small.IsSomeSet in H2. destruct H2 as [b H2].
  assert (b <> :0:) as H3. {
    apply NotEmptyToClass, NotEquivCompatL with A; assumption. }
  assert (exists a, a :< b /\ a :/\: b = :0:) as H4. {
    apply Foundation. assumption. }
  destruct H4 as [a [H4 H5]]. exists a. split.
  - apply H2. assumption.
  - apply DoubleNegation. intros H6. apply Class.Empty.HasElem in H6.
    destruct H6 as [x [H6 H7]]. apply ZF.Set.Empty.Charac with x.
    rewrite <- H5. apply ZF.Set.Inter2.Charac. split. 1: assumption.
    apply H2. assumption.
Qed.
