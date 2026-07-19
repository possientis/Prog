Require Import ZF.Class.Equiv.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Cofinal.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Inf.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Specify.

(* The character of cofinality of the ordinal a.                                *)
Definition charac (a:U) : U := inf {{ x :< succ a | Cofinal a }}.

(* The character of cofinality of an ordinal is contained in the ordinal.       *)
Proposition IsIncl : forall (a:U),
  Ordinal a -> charac a :<=: a.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a H1.
  (* The candidates are the ordinals below succ a cofinal with a.               *)
  remember {{ x :< succ a | Cofinal a }} as r eqn:Hr.
  assert (toClass r :<=: Ordinal) as H2. {
    intros x H2. rewrite Hr in H2. apply Specify.Charac in H2.
    destruct H2 as [H2 _]. apply Core.IsOrdinal with (succ a). 2: assumption.
    apply Succ.IsOrdinal. assumption. }
  assert (a :< r) as H3. {
    rewrite Hr. apply Specify.Charac. split.
    - apply Succ.IsIn.
    - apply Cofinal.Refl. assumption. }
  (* Since a is one of the candidates, their infimum is below a.                *)
  unfold charac. rewrite <- Hr. apply Inf.IsLowerBound; assumption.
Qed.

(* The character of cofinality of zero is zero.                                 *)
Proposition WhenZero : charac :0: = :0:.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  apply Empty.WhenIncl. apply IsIncl. apply Core.Zero.
Qed.
