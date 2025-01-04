Declare Scope ZF_Set_Eval_scope.
Open    Scope ZF_Set_Eval_scope.

Require Import ZF.Class.
Require Import ZF.Class.Compose.
Require Import ZF.Class.Domain.
Require Import ZF.Class.Eval.
Require Import ZF.Class.Functional.
Require Import ZF.Core.Dot.
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

Proposition EvalCompose : forall (F G:Class) (a:U),
  Functional F -> Functional G -> domain (G :.: F) a -> (G :.: F)!a = G!(F!a).
Proof.
  intros F G a' H1 H2 H3. remember H3 as H3' eqn:E. clear E.
  apply (proj1 (DomainCharac _ _)) in H3'.
  destruct H3' as [z' H3']. remember H3' as H12 eqn:E. clear E.
  apply ComposeCharac in H3'.
  destruct H3' as [a [y [z [H3' [H4 H5]]]]]. apply OrdPairEqual in H3'.
  destruct H3' as [H3' H6]. subst.
  assert (Functional (G :.: F)) as H7. { apply ComposeIsFunctional; assumption. }
  assert (domain F a) as H8. { apply DomainCharac. exists y. assumption. }
  assert (domain G y) as H9. { apply DomainCharac. exists z. assumption. }
  assert (F!a = y) as H10. { apply EvalWhenFunctional; assumption. } rewrite H10.
  assert (G!y = z) as H11. { apply EvalWhenFunctional; assumption. } rewrite H11.
  apply EvalWhenFunctional; assumption.
Qed.
