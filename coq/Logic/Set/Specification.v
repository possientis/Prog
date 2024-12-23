Require Import List.

Require Import Logic.Axiom.LEM.
Require Import Logic.Axiom.Dec.
Require Import Logic.Axiom.Wec.

Require Import Logic.List.Filter.

Require Import Logic.Set.Set.
Require Import Logic.Set.Incl.
Require Import Logic.Set.Elem.
Require Import Logic.Set.Equal.
Require Import Logic.Set.ToList.
Require Import Logic.Set.Compatible.
Require Import Logic.Set.Extensionality.

(* The axiom schema of specification is implied by that of replacement.         *)

(* Given a set x and a decidable predicate p (which may depend on x), returns   *)
(* the set of all elements y of x for which p y is true. There is no need to    *)
(* consider p a two variable predicate in order to make the possible dependency *)
(* in the set x explicit. This single variable formalism will do just as well.  *)
Definition comp (x:set)(p:set -> Prop)(q:pDec p) : set :=
    fromList (filter q (toList x)).

(* The predicate needs to be decidable and compatible.                          *)
Lemma compCharac : forall (x:set) (p:set -> Prop) (q:pDec p), 
    compatible p ->
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

(* Axiom schema of specification true in our model for decidable predicates.    *)
Theorem specificationDec : forall (p:set -> Prop), 
    pDec p ->
    compatible p ->
    forall (x:set), exists (y:set), forall (z:set), 
        z :: y <-> z :: x /\ p z.
Proof.
    intros p D C x. exists (comp x p D). apply compCharac. assumption.
Qed.

(* This is to emphasize that the predicate p above may depend on x. It is an    *)
(* immediate consequence of the main result so not very useful. It only serves  *)
(* to show there is no need to make dependency in x explicit in main result.    *)
Corollary specificationDec_ : forall (p:set -> set -> Prop), 
    pDec2 p          ->
    compatible2 p   ->
    forall (x:set), exists (y:set), forall (z:set), 
        z :: y <-> z :: x /\ p x z.  (* explicit dependency in x *)
Proof.
    intros p D C x. apply specificationDec.
    - apply pDec2Dec. assumption.
    - apply Comp2Comp. assumption. 
Qed.

(* Axiom schema of specification for weaker assumption of weak decidability.    *)
(* Again, there is no need to make possible dependency in x explicit in p.      *)
Theorem specificationDec' : forall (p:set -> Prop), 
    pWec p ->
    compatible p -> 
    forall (x:set), exists (y:set), forall (z:set), 
        z :: y <-> z :: x /\ p z.
Proof.
    intros p D C x. 
    remember (filterWec set p D (toList x)) as H eqn:E. clear E.
    destruct H as [ys H]. exists (fromList ys). intros z. split; intros H'.
    - apply toListElem in H'. destruct H' as [z' H']. 
      rewrite toListFromList in H'. destruct H' as [H0 [H1 H2]]. 
      remember (H z') as H3 eqn:E. clear E H. destruct H3 as [H3 H4]. 
      apply H4 in H0. destruct H0 as [H0 H5]. split.
        + apply toListElem. exists z'. split.
            {  assumption. }
            { split; assumption. }
        + unfold compatible in C. apply C with z'.
            { apply doubleIncl. split; assumption. }
            { assumption. }
    - destruct H' as [H0 H1]. rewrite toListElem in H0.
      destruct H0 as [z' [H0 [H2 H3]]]. apply toListElem. exists z'.
      rewrite toListFromList. split.
        + apply H. split.
            { assumption. }
            { unfold compatible in C. apply C with z.
                { apply doubleIncl. split; assumption. }
                { assumption. }}
        + split; assumption.
Qed.

(* Again, this is simply to demonstrate explicit dependency in x in not needed. *)
Corollary specificationDec'_ : forall (p:set -> set -> Prop), 
    pWec2 p ->
    compatible2 p -> 
    forall (x:set), exists (y:set), forall (z:set), 
        z :: y <-> z :: x /\ p x z.
Proof.
    intros p D C x. apply specificationDec'.
    - apply pWec2Wec. assumption.
    - apply Comp2Comp. assumption.
Qed.
