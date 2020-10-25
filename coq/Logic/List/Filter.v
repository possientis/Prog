Require Import List.

Require Import Logic.Axiom.LEM.
Require Import Logic.Axiom.Dec.
Require Import Logic.Axiom.Wec.

Require Import Logic.List.In.
Require Import Logic.List.Nil.

(* Given a predicate p and a 'proof' of decidability q we can filter a list.    *)
Fixpoint filter (a:Type) (p:a -> Prop) (q:pDec p) (xs:list a) : list a :=
    match xs with
    | nil       => nil
    | cons x xs => 
        match q x with  (* deciding whether p x holds or not                    *)
        | left  _   => cons x (filter a p q xs) (*  p x holds                   *)
        | right _   => filter a p q xs          (* ~p x holds                   *)
        end
    end.

Arguments filter {a} {p}.

(* Given a decidable predicate p and a list xs, saying that x lies in xs and    *)
(* satisfies the predicate p is equivalent to saying it lies in 'filter q xs'   *)
(* where 'q' is a witness to the decidability of p.                             *)
Lemma filterEquiv : forall (a:Type) (p:a -> Prop) (q:pDec p) (xs:list a) (x:a),
    x :: xs /\ p x <-> x :: filter q xs.
Proof.
    intros a p q xs x. induction xs as [|y xs IH].
    - simpl. split.
        + intros [H1 H2]. assumption.
        + intros H. exfalso. assumption.
    - split.
        + intros [[H1|H1] H2].
            { subst. destruct (q x) as [H|H] eqn:E.
                {simpl. rewrite E. left. reflexivity. }
                {exfalso. apply H. assumption. }}
            { destruct (q y) as [H|H] eqn:E; simpl; rewrite E.
                { right. apply IH. split; assumption. }
                { apply IH. split; assumption. }}
        + destruct (q y) as [H|H] eqn:E; simpl; rewrite E.
            { intros [H'|H'].
                { split; subst.
                    { left. reflexivity. }
                    { assumption. }}
                { apply IH in H'. destruct H' as [H1 H2]. split.
                    { right. assumption. }
                    { assumption. }}}
            { intros H'. apply IH in H'. destruct H' as [H1 H2]. split.
                    { right. assumption. }
                    { assumption. }}
Qed.

(* A list has an element which satisfies a given decidable predicate, if and    *)
(* only if the corresponding filtered list is not an empty list.                *)
Lemma filterNil : forall (a:Type) (p:a -> Prop) (q:pDec p) (xs:list a),
    (exists (x:a), In x xs /\ p x) <-> filter q xs <> nil.
Proof.
    intros a p q xs. split.
    - intros [x H]. apply nil_exists. exists x. apply filterEquiv. assumption.
    - intros H. apply nil_exists in H. destruct H as [x H]. exists x.
      apply (filterEquiv a p q). assumption.
Qed.

Arguments filterNil {a} {p}.

(* This is the main result of this module which we shall crucially use in order *)
(* to prove the decidability of set inclusion in our model. Given a decidable   *)
(* predicate p and a list xs, whether or not xs has an element which satisfies  *)
(* the predicate p is a decidable property.                                     *)
Theorem inPredDec : forall (a:Type) (p:a -> Prop) (q:pDec p) (xs:list a),
    {exists (x:a), In x xs /\ p x} + {~ exists (x:a), In x xs /\ p x}.
Proof.
    intros a p q xs. destruct (nil_Dec (filter q xs)) as [H|H] eqn:E.
    - right. intros H'. apply (filterNil q) in H'. apply H'. assumption.
    - left. apply (filterNil q). assumption.
Qed.

(* Assuming weak decidability of predicate p, which is implied by LEM.          *)
Lemma filterWec : forall (a:Type) (p:a -> Prop), pWec p -> 
    forall (xs:list a), exists (ys:list a), forall (x:a), 
        In x xs /\ p x <-> In x ys.
Proof.
    intros a p L. induction xs as [|x xs IH].
    - exists nil. intros z. split; intros H.
        + destruct H as [H0 H1]. assumption.
        + inversion H.
    - destruct IH as [ys IH]. destruct (L x) as [H|H].
        + exists (cons x ys). intros z. split; intros H'.
            { destruct H' as [[H0|H0] H1].
                { subst. left. reflexivity. }
                { right. apply IH. split; assumption. }}
            { destruct H' as [H0|H0].
                { subst. split.
                    { left. reflexivity. }
                    { assumption. }}
                { remember (IH z) as IH' eqn:E. clear E IH. apply IH' in H0.
                  clear IH'. destruct H0 as [H0 H1]. split.
                    { right. assumption. }
                    { assumption. }}}
        + exists ys. intros z. split; intros H'.
            { destruct H' as [[H0|H0] H1].
                { subst. apply H in H1. contradiction. }
                { apply IH. split; assumption. }}
            { remember (IH z) as IH' eqn:E. clear E IH.  apply IH' in H'.
              clear IH'. destruct H' as [H0 H1]. split.
                { right. assumption. }
                { assumption. }}
Qed.

(* This feels like an axiom schema of replacement for lists.                    *)
Lemma filterReplace : forall (a b:Type) (p:a -> b -> Prop),
    LEM                                                 ->
    (forall (x:a) (y y':b), p x y -> p x y' -> y = y')  ->
        forall (xs:list a), exists (ys:list b), forall (y:b),
            In y ys <-> exists (x:a), In x xs /\ p x y.
Proof.
    intros a b p L F. induction xs as [|x xs IH].
    - exists nil. intros y. split.
        + intros H. inversion H.
        + intros [x [H1 H2]]. inversion H1.
    - destruct IH as [ys IH]. destruct (L (exists (y:b), p x y)) as [H|H].
        + destruct H as [y H]. exists (cons y ys). intros z. split.
            { intros [H'|H'].
                { subst. exists x. split.
                    { left. reflexivity. }
                    { assumption. }}
                { destruct (IH z) as [H1 _]. apply H1 in H'. 
                  destruct H' as [x' [H2 H3]]. exists x'. split.
                    { right. assumption. }
                    { assumption. }}}
            { intros [x' [[H1|H1] H2]].
                { subst. left. apply F with x'; assumption. }
                { right. rewrite (IH z). exists x'. split; assumption. }}
        + exists ys. intros z. split.
            { intros H'. destruct (IH z) as [H1 _]. apply H1 in H'.
              destruct H' as [x' [H2 H3]]. exists x'. split.
                { right. assumption. }
                { assumption. }}
            { intros [x' [[H1|H1] H2]].
                { subst. exfalso. apply H. exists z. assumption. }
                { apply IH. exists x'. split; assumption. }}
Qed.
