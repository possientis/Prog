Require Import List.

Require Import Logic.List.In.
Require Import Logic.List.Include.

Declare Scope Equiv_scope.

Definition Equiv (v:Type) (xs ys:list v) : Prop :=
    (xs <= ys) /\ (ys <= xs).

Arguments Equiv {v}.

Notation "xs == ys" := (Equiv xs ys)
    (at level 70, no associativity) : Equiv_scope.

Open Scope Equiv_scope.

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

Lemma equivNil : forall (v:Type) (xs:list v),
    xs == nil <-> xs = nil.
Proof.
    intros v xs. split.
    - intros [H1 H2]. apply incl_nil. assumption.
    - intros H. rewrite H. apply equivRefl.
Qed.

Lemma equivConsCompat : forall (v:Type) (x:v) (xs ys:list v),
    xs == ys -> cons x xs == cons x ys.
Proof.
    intros v x xs ys [H1 H2]. split; intros z [H3|H3].
    - subst. left. reflexivity.
    - right. apply H1. assumption.
    - subst. left. reflexivity.
    - right. apply H2. assumption.
Qed.

Lemma inConsEquiv : forall (v:Type) (x:v) (xs:list v),
    x :: xs -> cons x xs == xs.
Proof.
    intros a x xs H. split; intros z.
    - intros [H1|H1].
        + subst. assumption.
        + assumption.
    - intros H1. right. assumption.
Qed.

Lemma equivCompatLR : forall (v:Type) (xs' ys' xs ys:list v),
    xs == xs' -> ys == ys' -> xs' == ys' -> xs == ys.
Proof.
    intros v xs' ys' xs ys H1 H2 H3. apply equivTrans with xs'.
    - assumption. 
    - apply equivTrans with ys'.
        + assumption.
        + apply equivSym. assumption.
Qed.
