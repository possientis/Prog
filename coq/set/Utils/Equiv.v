Require Import List.
 
Require Import Utils.Include.

Definition Equiv (a:Type) (xs ys:list a) : Prop :=
    incl xs ys /\ incl ys xs.

Arguments Equiv {a}.

Lemma equivRefl : forall (a:Type) (xs:list a), Equiv xs xs.
Proof. intros a xs. split; apply incl_refl. Qed.

Lemma equivSym : forall (a:Type) (xs ys:list a), Equiv xs ys -> Equiv ys xs.
Proof. intros a xs ys [H1 H2]. split; assumption. Qed.

Lemma equivTrans : forall (a:Type) (xs ys zs:list a), 
    Equiv xs ys -> Equiv ys zs -> Equiv xs zs.
Proof.
    intros a xs ys zs [H1 H2] [H3 H4]. 
    split; apply incl_tran with ys; assumption.
Qed.

Lemma inConsEquiv : forall (a:Type) (x:a) (xs:list a),
    In x xs -> Equiv (cons x xs) xs.
Proof.
    intros a x xs H. split; intros z.
    - intros [H1|H1].
        + subst. assumption.
        + assumption.
    - intros H1. right. assumption.
Qed.

Lemma equivNil : forall (a:Type) (xs:list a),
    Equiv xs nil <-> xs = nil.
Proof.
    intros a xs. split; intros H.
    - destruct H as [H1 H2]. apply inclNil. assumption.
    - rewrite H. apply equivRefl.
Qed.

