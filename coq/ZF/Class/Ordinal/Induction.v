Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Diff.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.Less.
Require Import ZF.Class.Ordinal.Core.

(* Principle of transfinite induction.                                          *)
Proposition Induction : forall (A:Class),
  A :<=: On                                   ->
  (forall a, On a -> toClass a :<=: A -> A a) ->
  A :~: On.
Proof.
  intros A H1 H2. apply DoubleNegation. intros H3.
  assert (On :\: A :<>: :0:) as H4. { apply Diff.WhenLess. split; assumption. }
  assert (exists a, (On :\: A) a /\ (On :\: A) :/\: toClass a :~: :0:) as H5. {
    apply HasEMinimal with On. 3: assumption.
    - apply OnIsOrdinal.
    - apply Class.Inter2.IsInclL. }
  destruct H5 as [a [[H5 H6] H7]]. assert (toClass a :<: On) as H8. {
    apply Class.Ordinal.Core.LessIsElem; try assumption. apply OnIsOrdinal. }
  assert (toClass a :<=: A) as H9. {
    intros x H10. apply DoubleNegation. intros H11.
    apply Class.Empty.Charac with x, H7. split. 2: assumption. split. 2: assumption.
    apply Class.Ordinal.Core.IsOrdinal with (toClass a); assumption. }
  apply H6, H2; assumption.
Qed.
