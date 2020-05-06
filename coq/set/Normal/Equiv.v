Require Utils.Equiv.

Require Import Core.Set.
Require Import Normal.Leq.

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
