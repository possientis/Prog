Require Import ZF.Class.Core.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Foundation.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.Order.Founded.
Require Import ZF.Class.Order.Minimal.
Require Import ZF.Class.Relation.Fun.
Require Import ZF.Class.Relation.FunctionOn.
Require Import ZF.Class.Relation.Range.
Require Import ZF.Set.Core.
Require Import ZF.Set.Ordinal.Omega.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.EvalOfClass.

(* There is no infinite descending :<-chain.                                    *)
Proposition NoInfiniteDescent : forall (F:Class),
  FunctionOn F (toClass :N) -> exists n, n :< :N /\ ~ F!(succ n) :< F!n.
Proof.
  intros F H1.
  assert (exists a, range F a /\ toClass a :/\: range F :~: :0: ) as H2. {
    apply Foundation.
    - apply FunctionOn.RangeIsNotEmpty with (toClass :N). 1: assumption.
      apply NotEmptyToClass, Omega.IsNotEmpty.
    - apply FunctionOn.RangeIsSmall with (toClass :N). 1: assumption.
      apply Small.EquivCompat with :N.
      + apply EquivSym, Omega.ToClass.
      + apply Omega.IsSmall. }
  destruct H2 as [a [H2 H3]].
  apply (FunctionOn.RangeCharac F (toClass :N)) in H2. 2: assumption.
  destruct H2 as [n [H2 H4]]. exists n. split. 1: assumption. intros H5.
  apply Class.Empty.Charac with (F!(succ n)). apply H3. split.
  - rewrite H4. assumption.
  - apply FunctionOn.EvalIsInRange with (toClass :N). 1: assumption.
    apply Omega.HasSucc. assumption.
Qed.

(* There is no infinite descending R-chain when R is founded.                   *)
Proposition NoInfiniteDescentFounded : forall (F R A:Class),
  Fun F (toClass :N) A        ->
  Founded R A                 ->
  exists n, n :< :N /\ ~ R :(F!(succ n),F!n):.
Proof.
  intros F R A H1 H2.
  assert (exists a, Minimal R (range F) a) as H3. {
    apply Founded.WhenSmall with A. 1: assumption.
    - apply Fun.RangeIsSmall with (toClass :N) A. 1: assumption.
      apply Small.EquivCompat with :N. 2: apply Omega.IsSmall.
      apply EquivSym, Omega.ToClass.
    - apply H1.
    - apply Fun.RangeIsNotEmpty with (toClass :N) A. 1: assumption.
      apply NotEmptyToClass, Omega.IsNotEmpty. }
  destruct H3 as [a H3].
  assert (range F a) as H4. { apply Minimal.IsIn with R. assumption. }
  apply (Fun.RangeCharac F (toClass :N) A) in H4. 2: assumption.
  destruct H4 as [n [H4 H5]]. exists n. split. 1: assumption.
  revert H3. rewrite <- H5. apply Minimal.HasNoLesser.
  apply FunctionOn.EvalIsInRange with (toClass :N). 1: apply H1.
  apply Omega.HasSucc. assumption.
Qed.
