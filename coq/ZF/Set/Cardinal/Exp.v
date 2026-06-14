Require Import ZF.Set.Cardinal.Equiv.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.Power.
Require Import ZF.Set.Relation.Charac.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Fiber.
Require Import ZF.Set.Relation.Bij.
Require Import ZF.Set.Relation.Fun.
Require Import ZF.Set.Relation.Fun.From.
Require Import ZF.Set.Relation.Map.

Require Import ZF.Notation.Exp2.
Export ZF.Notation.Exp2.

(* The exponentiation of two sets.                                              *)
Definition exp (a b:U) : U := map b a.


(* Notation "a :^^: b" := (exp a b)                                             *)
Global Instance SetExp2 : Exp2 U := { exp2 := exp }.

(* The set of maps from a into two is equipotent to the power set of a.         *)
Proposition OfTwo : forall (a:U),
  :2: :^^: a :~: :P(a).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a. unfold exp.
  (* Send a two-valued function to its fiber over one.                          *)
  remember (from (map a :2:) (fun f => fiber f :1:)) as h eqn:H1.
  assert (Bij h (map a :2:) :P(a)) as H2. {
    rewrite H1. apply From.IsBij.
    - (* The fiber over one is a subset of the domain, hence a subset of a.     *)
      intros f H2. apply Power.Charac.
      assert (Fun f a :2:) as H3. { apply CharacMap. assumption. }
      assert (domain f = a) as H4. { apply H3. }
      rewrite <- H4. apply Fiber.IsIncl.
    - (* Binary-valued functions are determined by their fibers over one.       *)
      intros f g H2 H3 H4. apply Fiber.EqualOfOne with a; try assumption;
        apply CharacMap; assumption.
    - (* Every subset of a is the fiber over one of its characteristic function.*)
      intros b H2.
      assert (b :<=: a) as H3. { apply Power.Charac. assumption. }
      exists (charac a b). split.
      + apply CharacMap. apply Charac.IsFun.
      + apply Fiber.OfCharac. assumption. }
  exists h. assumption.
Qed.
