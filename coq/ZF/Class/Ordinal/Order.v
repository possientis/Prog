Require Import ZF.Class.Core.
Require Import ZF.Class.Diff.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Incl.
Require Import ZF.Class.IsSetOf.
Require Import ZF.Class.Order.E.
Require Import ZF.Class.Order.Isom.
Require Import ZF.Class.Order.Minimal.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.Inf.
Require Import ZF.Class.Ordinal.Transitive.
Require Import ZF.Set.Core.
Require Import ZF.Set.Eval.
Require Import ZF.Set.Foundation.

(* An element a of an ordinal class A is a :<-minimal element of A\a.           *)
Proposition IsEMinimal : forall (A:Class) (a:U),
  Ordinal A ->
  A a       ->
  Minimal E (A :\: toClass a) a.
Proof.
  intros A a H1 H2.
  assert (On a) as H3. { apply Class.Ordinal.Core.IsOrdinal with A; assumption. }
  assert (A :\: toClass a :<>: :0:) as H4. {
    apply Class.Empty.HasElem. exists a. split. 1: assumption. apply NoElemLoop1. }
  apply Inf.IsEMinimal. 2: assumption.
  - intros x [H5 _]. apply Class.Ordinal.Core.IsOrdinal with A; assumption.
  - apply Inf.WhenOrdinal; assumption.
Qed.

Proposition IsomIsId : forall (F A B:Class),
  Ordinal A       ->
  Ordinal B       ->
  Isom F E E A B  ->
  forall (a:U), A a -> F!a = a.
Proof.
  intros F A B H1 H2 H3.
  remember (fun a => On a /\ (A a -> F!a = a)) as C eqn:H4.
  assert (C :~: On) as H5. {
    apply Core.TransfiniteInduction.
    - intros a H5. rewrite H4 in H5. destruct H5 as [H5 _]. assumption.
    - intros b H5 H6. rewrite H4. split. 1: assumption. intros H7.
      assert (forall a, a :< b -> F!a = a) as H8. {
        intros a H8.
        assert (C a) as H9. { apply H6. assumption. }
        rewrite H4 in H9. destruct H9 as [H9 H10]. apply H10.
        assert (H11 := H1). destruct H11 as [H11 _].
        apply H11 with b; assumption. }
Admitted.

(*
  intros a H6.
  assert (On a) as H7. { apply Core.IsOrdinal with A; assumption. }
  assert (C a) as H8. { apply H5. assumption. }
  rewrite H4 in H8. destruct H8 as [_ H8]. apply H8. assumption.
Qed.
*)
(*
  assert (C a) as H8. { apply H5. assumption. }
  rewrite H4 in H8. apply H8. split; assumption.
Qed.
*)
(*
Proposition IsomIsEquiv : forall (F A B:Class), Ordinal A -> Ordinal B ->
  Isom F E E A B -> A :~: B.
Proof.

Show.
*)
