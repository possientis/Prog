Require Import ZF.Class.
Require Import ZF.Class.Compose.
Require Import ZF.Class.Converse.
Require Import ZF.Class.Domain.
Require Import ZF.Class.Function.
Require Import ZF.Class.OneToOne.
Require Import ZF.Class.Rel.
Require Import ZF.Core.Dot.
Require Import ZF.Core.Equiv.

(* A class is a bijection if it is a relation and it is one-to-one.             *)
Definition Bijection (F:Class) : Prop := Rel F /\ OneToOne F.

(* F is a bijection defined on A.                                               *)
Definition BijectionOn (F A:Class) : Prop := Bijection F /\ domain F :~: A.

Proposition BijectionIsFunction : forall (F:Class),
  Bijection F -> Function F.
Proof.
  intros F [H1 [H2 H3]]. split; assumption.
Qed.

Proposition BijectionConverseIsFunction : forall (F:Class),
  Bijection F -> Function (converse F).
Proof.
  intros F [H1 [H2 H3]]. split.
  - apply ConverseIsRel.
  - apply H3.
Qed.

Proposition ComposeIsBijection : forall (F G:Class),
  OneToOne F -> OneToOne G -> Bijection (G :.: F).
Proof.
  intros F G Hf Hg. split.
  - apply ComposeIsRel.
  - apply ComposeIsOneToOne; assumption.
Qed.

(* Weaker result but convenient                                                 *)
Proposition ComposeIsBijection2 : forall (F G:Class),
  Bijection F -> Bijection G -> Bijection (G :.: F).
Proof.
  intros F G [_ Hf] [_ Hg]. apply ComposeIsBijection; assumption.
Qed.
