Require Import List.

Require Import Core.Set.
Require Import Core.Incl.
Require Import Core.Elem.
Require Import Core.Equal.
Require Import Core.Filter.
Require Import Core.ToList.
Require Import Core.Compatible.
Require Import Core.Extensionality.

(* Given a set x and a decidable predicate p, creates a set made of all those   *)
(* elements of x which satisfy the predicate p.                                 *)
Definition comp (x:set)(p:set -> Prop)(q:Dec p) : set :=
    fromList (filter q (toList x)).


(* The predicate needs to be decidable and compatible.                          *)
Lemma compCharac : forall (x:set) (p:set -> Prop) (q:Dec p), compatible p ->
    forall (z:set), z :: comp x p q <-> z :: x /\ p z.
Proof.
    intros x p q C z. unfold comp. split; intros H.
    - apply toListElem in H. destruct H as [y [H1 [H2 H3]]].
      rewrite toListFromList in H1. rewrite <- filterEquiv in H1.
      destruct H1 as [H0 H1]. split.
        + apply toListElem. exists y. split.
            { assumption. }
            { split; assumption. }
        + unfold compatible in C. apply C with y.
            { apply doubleIncl. split; assumption. }
            { assumption. }
    - destruct H as [H0 H1]. apply toListElem. apply toListElem in H0.
      destruct H0 as [y [H0 [H2 H3]]]. exists y. rewrite toListFromList. split.
        + apply filterEquiv. split.
            { assumption. }
            { unfold compatible in C. apply C with z.
                { apply doubleIncl. split; assumption. }
                { assumption. }}
        + split; assumption.
Qed.
  
Theorem comprehensionDec : forall (p:set -> Prop) (q:Dec p), compatible p ->
    forall (x:set), exists (y:set), forall (z:set), z :: y <-> z :: x /\ p z.
Proof.
    intros p q C x. exists (comp x p q). apply compCharac. assumption.
Qed.
