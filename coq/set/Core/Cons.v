(* NEXT: ===> Filter                                                            *) 


Require Import Core.Set.
Require Import Core.Incl.
Require Import Core.Elem.
Require Import Core.Trans.
Require Import Core.Equal.
Require Import Core.ToList.
Require Import Core.Extensionality.



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

