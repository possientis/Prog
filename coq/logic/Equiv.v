Require Import List.

Require Import Include.

Definition Equiv (v:Type) (xs ys:list v) : Prop :=
    (xs <= ys) /\ (ys <= xs).

Arguments Equiv {v}.

Notation "xs == ys" := (Equiv xs ys)
    (at level 70, no associativity) : Equiv_scope.

Open Scope Equiv_scope.


Lemma equivNilIsNil : forall (v:Type) (xs:list v),
    xs == nil -> xs = nil.
Proof.
    intros v xs [H1 H2]. apply incl_nil. assumption.
Qed.

Lemma equivRefl : forall (v:Type) (xs:list v), xs == xs.
Proof.
    intros v xs. split; apply incl_refl.
Qed.

Lemma equivSym : forall (v:Type) (xs ys:list v), 
    xs == ys -> ys == xs.
Proof.
    intros v xs ys [H1 H2]. split; assumption.
Qed.

Lemma equivTrans : forall (v:Type) (xs ys zs:list v),
    xs == ys -> ys == zs -> xs == zs.
Proof.
    intros v xs ys zs [H1 H2] [H3 H4]. split;
    apply incl_tran with ys; assumption.
Qed.
