(* NEXT: ===> Filter                                                            *) 


Require Import Logic.Set.Set.
Require Import Logic.Set.Incl.
Require Import Logic.Set.Elem.
Require Import Logic.Set.Trans.
Require Import Logic.Set.Equal.
Require Import Logic.Set.ToList.
Require Import Logic.Set.Extensionality.



(* The following lemma will prove very useful in many places. Note that the     *)
(* statement of this lemma involves the constructor 'Cons' which is not a       *)
(* primitive of a core set theoretic language. So this lemma, like many of the  *)
(* results we have proved until now, can be regarded as a lemma of the 'meta'   *)
(* theory. It is not a lemma of set theory itself.                              *)
Lemma consElem : forall (x xs z:set), z :: Cons x xs <-> (z == x) \/ z :: xs.
Proof.
    intros x xs z. split.
    - intros H. apply toListElem in H. simpl in H.
      destruct H as [z' [[H1|H1] [H2 H3]]].
        + subst. left. apply doubleIncl. split; assumption.
        + right. apply toListElem. exists z'. split.
            { assumption. }
            { split; assumption. }
    - intros [H|H].
        + apply toListElem. exists x. split.
            { left. reflexivity. }
            { apply doubleIncl. assumption. }
        + apply toListElem. apply toListElem in H.
          destruct H as [z' [H1 [H2 H3]]]. exists z'. split.
            { right. assumption. }
            { split; assumption. }
Qed.


Lemma consCompatL : forall (x x' xs:set), x == x' -> Cons x xs == Cons x' xs.
Proof.
    intros x x' xs H. apply extensionality. intros z. split; intros H';
    rewrite consElem in H'; destruct H' as [H'|H']; apply consElem.
    - left.  apply equalTrans with x; assumption.
    - right. assumption.
    - left. apply equalTrans with x'.
        + assumption.
        + apply equalSym. assumption.
    - right. assumption.
Qed.


Lemma consCompatR : forall (x xs xs':set), xs == xs' -> Cons x xs == Cons x xs'.
Proof.
    intros x xs xs' H. apply extensionality. intros z. split; intros H';
    rewrite consElem in H'; destruct H' as [H'|H']; apply consElem.
    - left. assumption.
    - right. apply elemCompatR with xs; assumption.
    - left. assumption.
    - right. apply elemCompatR with xs'.
        + apply equalSym. assumption.
        + assumption.
Qed.

Lemma consCompatLR : forall (x x' xs xs':set),
    x == x' -> xs == xs' -> Cons x xs == Cons x' xs'.
Proof.
    intros x x' xs xs' H1 H2. apply equalTrans with (Cons x' xs).
    - apply consCompatL. assumption.
    - apply consCompatR. assumption.
Qed.

Lemma consSwitch : forall (x y zs:set), Cons x (Cons y zs) == Cons y (Cons x zs).
Proof.
    intros x y zs. apply extensionality. intros z. split; intros H;
    rewrite consElem in H; rewrite consElem in H; destruct H as [H1|[H1|H1]];
    apply consElem; rewrite consElem.
    - right. left. assumption.
    - left. assumption.
    - right. right. assumption.
    - right. left. assumption.
    - left. assumption.
    - right. right. assumption.
Qed.


Lemma inConsEqual : forall (x xs:set), x :: xs -> Cons x xs == xs.
Proof.
    intros x xs H. apply extensionality. intros z. split; intros H'.
    - rewrite consElem in H'. destruct H' as [H'|H'].
        + apply elemCompatL with x.
            { apply equalSym. assumption. }
            { assumption. }
        + assumption.
    - apply consElem. right. assumption.
Qed.
