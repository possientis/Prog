Require Import ZF.Class.
Require Import ZF.Class.Compose.
Require Import ZF.Class.Functional.
Require Import ZF.Class.Relation.
Require Import ZF.Core.Dot.

(* A class is a function if it is a relation and it is functional.              *)
Definition Function (P:Class) : Prop := Relation P /\ Functional P.

Proposition ComposeIsFunction : forall (P Q:Class),
  Functional P -> Functional Q -> Function (Q :.: P).
Proof.
  intros P Q Hp Hq. split.
  - apply ComposeIsRelation.
  - apply ComposeIsFunctional; assumption.
Qed.

(* Weaker result but convenient                                                 *)
Proposition ComposeIsFunction2 : forall (P Q:Class),
  Function P -> Function Q -> Function (Q :.: P).
Proof.
  intros P Q [_ Hp] [_ Hq]. apply ComposeIsFunction; assumption.
Qed.
