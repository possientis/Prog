Require Import ZF.Class.
Require Import ZF.Class.Compose.
Require Import ZF.Class.Domain.
Require Import ZF.Class.Functional.
Require Import ZF.Class.Rel.
Require Import ZF.Core.Dot.
Require Import ZF.Core.Equiv.
Require Import ZF.Set.
Require Import ZF.Set.Eval.

(* A class is a function iff it is a relation and it is functional.             *)
Definition Function (F:Class) : Prop := Rel F /\ Functional F.

Proposition ComposeIsFunction : forall (F G:Class),
  Functional F -> Functional G -> Function (G :.: F).
Proof.
  intros F G Hf Hg. split.
  - apply ComposeIsRelation.
  - apply ComposeIsFunctional; assumption.
Qed.

(* Weaker result but convenient                                                 *)
Proposition ComposeIsFunction2 : forall (F G:Class),
  Function F -> Function G -> Function (G :.: F).
Proof.
  intros F G [_ Hf] [_ Hg]. apply ComposeIsFunction; assumption.
Qed.

Proposition FunctionEquivCharac : forall (F G:Class), F :~: G <->
  domain F :~: domain G  /\ forall x, domain F x -> F:(x): = G:(x):.
Proof.
  intros F G. split; intros H1.
  - split.
    + apply DomainEquivCompat. assumption.
    + intros x H2.
Admitted.
