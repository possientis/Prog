(* NEXT: ===> Filter                                                      *) 


Require Import Core.Set.
Require Import Core.Incl.
Require Import Core.Elem.
Require Import Core.ToList.
Require Import Core.Trans.
Require Import Core.ElemIncl.
Require Import Core.Equal.

(* The extensionality axiom is one of the axioms of Zermelo-Fraenkel set theory *)
(* aka 'ZF'. It expresses the fact that two sets are equal if and only if they  *)
(* have identical elements. This axiom is true in our model. It is not obvious  *)
(* that this should be the case, as we have defined equality between sets as a  *)
(* stronger property than simply having identical elements. So this axiom is a  *)
(* strong result, and it is effectively saying there is no need to check that   *)
(* two sets belong to the same sets in order to establish their equality.       *)
(* The statement of extensionality is an axiom in standard set theory. But of   *)
(* course we are defining a model of set theory within Coq. So extensionality   *)
(* is not an axiom in this case. It is something we prove from the Coq logical  *)
(* system and our definitions of the type 'set' and the relations '::' and '==' *)
Theorem extensionality : forall (x y:set),
    x == y <-> forall (z:set), z :: x <-> z :: y.
Proof.
    intros x y. split.
    - intros [H1 H2]. assumption. 
    - intros H. split.
        + assumption.
        + intros z. split; intros H'; apply toListElem in H'.
            { destruct H' as [x' [H1 [H2 H3]]]. 
              apply toListElem. exists x'. split.
                { assumption. }
                { split.
                    { apply inclTrans with x.
                        { apply elemIncl. apply H. }
                        { assumption. }}
                    { apply inclTrans with x.
                        { assumption. }
                        { apply elemIncl. apply H. }}}}
            { destruct H' as [y' [H1 [H2 H3]]]. 
              apply toListElem. exists y'. split.
                { assumption. }
                { split.
                    { apply inclTrans with y.
                        { apply elemIncl. apply H. }
                        { assumption. }}
                    { apply inclTrans with y.
                        { assumption. }
                        { apply elemIncl. apply H. }}}}
Qed.

(* A consequence of extensionality is that equality is equivalent to double     *)
(* inclusion. So while we were very careful to define equality in the proper    *)
(* way, in the end we have a notion which is no stronger than double inclusion. *)
Theorem doubleIncl : forall (x y:set), 
    x == y <-> (x <== y) /\ (y <== x).
Proof.
    intros x y. split.
    - intros H. destruct H as [H1 H2]. split; apply elemIncl; apply H1.
    - intros [H1 H2]. apply extensionality. intros z. split; intros H.
        + rewrite elemIncl in H1. apply H1. assumption.
        + rewrite elemIncl in H2. apply H2. assumption.
Qed.

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

