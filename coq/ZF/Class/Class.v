Require Import ZF.Axiom.Core.
Require Import ZF.Core.Equiv.

(* A class is simply a predicate on sets.                                       *)
Definition Class : Type := U -> Prop.

(* Natural equivalence between classes.                                         *)
Definition classEquiv (P Q:Class) : Prop := forall x, P x <-> Q x.

Global Instance ClassEquiv : Equiv Class := {
  equiv := classEquiv
}.

Proposition ClassEquivCharac : forall (P Q:Class),
  P == Q <-> forall x, P x <-> Q x.
Proof.
  intros P Q. split; intros H1.
  - apply H1.
  - unfold equiv, ClassEquiv, classEquiv. apply H1.
Qed.


