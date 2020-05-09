Require Utils.Equiv.

Require Import Core.Set.
Require Import Normal.Leq.
Require Import Normal.InListOf.

Definition Equiv (x y:set) : Prop := 
    Equiv.Equiv (toList x) (toList y).

Lemma equivRefl : forall (x:set), Equiv x x.
Proof.
    intros x. unfold Equiv. apply Equiv.equivRefl.
Qed.

Lemma equivSym : forall (x y:set), Equiv x y -> Equiv y x.
Proof.
    intros x y. unfold Equiv. apply Equiv.equivSym.
Qed.

Lemma equivTrans : forall (x y z:set),
    Equiv x y -> Equiv y z -> Equiv x z.
Proof.
    intros x y z. unfold Equiv. apply Equiv.equivTrans.
Qed.

Lemma consIn : forall (x xs:set),
    inListOf x xs -> Equiv (Cons x xs) xs.
Proof.
    intros x xs. unfold Equiv. unfold inListOf. simpl.
    apply Equiv.consIn.
Qed.

Lemma equivNil : forall (x:set), Equiv x Nil <-> x = Nil.
Proof.
    intros x. unfold Equiv. simpl. split; intros H.
    - apply Equiv.equivNil in H. rewrite <- (fromListToList x).
      rewrite H. reflexivity.
    - apply Equiv.equivNil. rewrite H. reflexivity.
Qed.
