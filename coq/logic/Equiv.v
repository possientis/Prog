Require Import List.

Require Import Include.

Definition Equiv (v:Type) (xs ys:list v) : Prop :=
    (xs <= ys) /\ (ys <= xs).

Arguments Equiv {v}.

Notation "xs == ys" := (Equiv xs ys)
    (at level 70, no associativity) : Equiv_scope.

Open Scope Equiv_scope.


Lemma EquivNilIsNil : forall (v:Type) (xs:list v),
    xs == nil -> xs = nil.
Proof.
    intros v xs [H1 H2]. apply incl_nil. assumption.
Qed.

