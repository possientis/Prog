Require Utils.Equiv.
Require List.

Require Import Core.Set.
Require Import Core.Incl.
Require Import Core.Elem.
Require Import Core.Equal.
Require Import Core.ToList.
Require Import Core.ElemIncl.
Require Import Core.Extensionality.

Require Import Normal.Leq.
Require Import Normal.InListOf.

(* Two sets have same syntactic elements                                        *)
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

Lemma inclIncl : forall (x y:set),
    List.incl (toList x) (toList y) -> x <== y.
Proof.
    intros x y H1. apply elemIncl. intros z H2.
    rewrite toListElem in H2. destruct H2 as [z' [H2 [H3 H4]]].
    apply toListElem. exists z'. split.
    - apply H1. assumption.
    - split; assumption.
Qed.

Lemma equivEqual : forall (x y:set), Equiv x y -> x == y.
Proof.
    intros x y. unfold Equiv, Equiv.Equiv. intros [H1 H2].
    apply doubleIncl. split; apply inclIncl; assumption.
Qed.
