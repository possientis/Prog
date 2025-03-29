Require Import ZF.Class.
Require Import ZF.Class.Diff.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Functional.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Range.
Require Import ZF.Class.Restrict.
Require Import ZF.Class.Small.
Require Import ZF.Set.

Proposition LesserThanRangeOfRestrict : forall (F A:Class),
  Functional F ->
  (exists a, A :\: range (F:|:toClass a) :~: :0:) ->
  Small A.
Proof.
  intros F A H1 [a H2]. apply Diff.WhenEmpty in H2.
  apply LesserThanRangeOfRestrictIsSmall with F (toClass a).
  - assumption.
  - apply SetIsSmall.
  - assumption.
Qed.
