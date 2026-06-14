Require Import ZF.Class.Equiv.
Require Import ZF.Set.Core.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.Pair.
Require Import ZF.Set.Relation.Fun.
Require Import ZF.Set.Relation.Fun.IfThenElse.

Require Import ZF.Notation.Eval.


Definition charac (a b:U) : U :=
  ifThenElse a (toClass b) (fun _ => :1:) (fun _ => :0:).

(* The characteristic function of b on a maps a to two.                         *)
Proposition IsFun : forall (a b:U), Fun (charac a b) a :2:.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b. apply IfThenElse.IsFun. split.
  (* The value one belongs to two.                                              *)
  - intros x H1 H2. rewrite Natural.TwoExtension. apply Pair.IsInR.
  (* The value zero belongs to two.                                             *)
  - intros x H1 H2. rewrite Natural.TwoExtension. apply Pair.IsInL.
Qed.

(* The characteristic function has value one on elements of b.                  *)
Proposition EvalIn : forall (a b x:U),
  x :< a -> x :< b -> (charac a b)!x = :1:.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b x H1 H2. unfold charac. apply IfThenElse.Eval1; assumption.
Qed.

(* The characteristic function has value zero away from b.                      *)
Proposition EvalOut : forall (a b x:U),
  x :< a -> ~ x :< b -> (charac a b)!x = :0:.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b x H1 H2. unfold charac. apply IfThenElse.Eval2; assumption.
Qed.
