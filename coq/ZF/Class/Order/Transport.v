Require Import ZF.Class.Equiv.
Require Import ZF.Class.Relation.Bij.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.EvalOfClass.

(* Transporting a 'relation R on A' by F.                                       *)
Definition transport (F R A:Class) : Class := fun x =>
  exists y z, x = :(F!y,F!z): /\ A y /\ A z /\ R :(y,z):.

Proposition Charac2F : forall (F R A B:Class) (y z:U),
  Bij F A B ->
  A y       ->
  A z       ->
  transport F R A :(F!y,F!z): <-> A y /\ A z /\ R :(y,z):.
Proof.
  intros F R A B y z H1 H2 H3. split; intros H4.
  - destruct H4 as [y' [z' [H4 [H5 [H6 H7]]]]]. apply WhenEqual in H4.
    destruct H4 as [H4 H8].
    assert (y = y') as H9.  { apply Bij.EvalInjective with F A B; assumption. }
    assert (z = z') as H10. { apply Bij.EvalInjective with F A B; assumption. }
    subst. split. 1: assumption. split; assumption.
  - destruct H4 as [H4 [H5 H6]]. exists y. exists z. split.
    1: reflexivity. split. 1: assumption. split; assumption.
Qed.


