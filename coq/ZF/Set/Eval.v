Declare Scope ZF_Set_Eval_scope.
Open    Scope ZF_Set_Eval_scope.

Require Import ZF.Class.
Require Import ZF.Class.Domain.
Require Import ZF.Class.Eval.
Require Import ZF.Class.Functional.
Require Import ZF.Core.Equiv.
Require Import ZF.Set.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.OrdPair.

Definition eval (F:Class) (a:U) : U := fromClass (Class.Eval.eval F a)
  (EvalIsSmall F a).

Notation "F ! a" := (eval F a)
  (at level 0, no associativity) : ZF_Set_Eval_scope.

Proposition EvalWhenFunctional : forall (F:Class) (a y:U),
  Functional F -> domain F a -> F :(a,y): <-> F!a = y.
Proof.
  intros F a y H1 H2. split; intros H3.
  - apply SameClassEqual. unfold eval.
    apply ClassEquivTran with (Class.Eval.eval F a).
    + apply ToClassFromClass.
    + apply Class.Eval.EvalWhenFunctional; assumption.
  - apply Class.Eval.EvalWhenFunctional.
    + assumption.
    + assumption.
    + rewrite <- H3. unfold eval. apply ClassEquivSym, ToClassFromClass.
Qed.
