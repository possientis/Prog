

Require Import List.

Require Import Utils.LEM.
Require Import Utils.Decidable.

(* In this module, we are having a small interlude focussing on decidability    *)
(* results which are specific to the Coq meta-theory, and are not set theoretic *)
(* results. These results are interesting in their own rights, but will also    *)
(* prove useful when attempting to establish some set theoretic properties of   *)
(* our model. By default, the Coq logical system does not allow us to assume    *)
(* the 'law of excluded middle' aka 'LEM'. We could postulate LEM as an axiom   *)
(* of our meta-theory (which is known to be consistent with Coq's logic) but    *)
(* we should remember that our model is just a simple model of finite sets in   *)
(* which many things can be proven without using LEM. Our first objective is to *)
(* define the function 'filter' allowing us to restrict a list of sets to a     *)
(* list of sets satisfying a given decidable predicate.                         *)
    
(* Given a predicate p and a 'proof' of decidability q we can filter a list.    *)
Fixpoint filter (a:Type) (p:a -> Prop) (q:Dec p) (xs:list a) : list a :=
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
Lemma filterEquiv : forall (a:Type) (p:a -> Prop) (q:Dec p) (xs:list a) (x:a),
    In x xs /\ p x <-> In x (filter q xs).
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

(* A list is not empty if and only if it has an element which lies in it.       *)
Lemma existsNil : forall (a:Type) (xs:list a),
    (exists (x:a), In x xs) <-> xs <> nil.
Proof.
    intros a xs. destruct xs as [|x xs]; split.
    - intros [x H]. inversion H.
    - intros H. exfalso. apply H. reflexivity.
    - intros H1 H2. inversion H2.
    - intros H. exists x. left. reflexivity.
Qed.

(* A list has an element which satisfies a given decidable predicate, if and    *)
(* only if the corresponding filtered list is not an empty list.                *)
Lemma filterNil : forall (a:Type) (p:a -> Prop) (q:Dec p) (xs:list a),
    (exists (x:a), In x xs /\ p x) <-> filter q xs <> nil.
Proof.
    intros a p q xs. split.
    - intros [x H]. apply existsNil. exists x. apply filterEquiv. assumption.
    - intros H. apply existsNil in H. destruct H as [x H]. exists x.
      apply (filterEquiv a p q). assumption.
Qed.

Arguments filterNil {a} {p}.

(* Whether a list is the empty list or not is decidable.                        *)
Lemma nilDec : forall (a:Type) (xs:list a), {xs = nil} + {xs <> nil}.
Proof.
    intros a xs. destruct xs as [|x xs].
    - left. reflexivity.
    - right. intros H. inversion H.
Qed.


Arguments nilDec {a}.

(* This is the main result of this module which we shall crucially use in order *)
(* to prove the decidability of set inclusion in our model. Given a decidable   *)
(* predicate p and a list xs, whether or not xs has an element which satisfies  *)
(* the predicate p is a decidable property.                                     *)
Theorem inPredDec : forall (a:Type) (p:a -> Prop) (q:Dec p) (xs:list a),
    {exists (x:a), In x xs /\ p x} + {~ exists (x:a), In x xs /\ p x}.
Proof.
    intros a p q xs. destruct (nilDec (filter q xs)) as [H|H] eqn:E.
    - right. intros H'. apply (filterNil q) in H'. apply H'. assumption.
    - left. apply (filterNil q). assumption.
Qed.


Lemma filterLEM : forall (a:Type) (p:a -> Prop), LEM -> forall (xs:list a), 
    exists (ys:list a), forall (x:a), In x xs /\ p x <-> In x ys.
Proof.
    intros a p L. induction xs as [|x xs IH].
    - exists nil. intros z. split; intros H.
        + destruct H as [H0 H1]. assumption.
        + inversion H.
    - destruct IH as [ys IH]. unfold LEM in L. destruct (L (p x)) as [H|H].
        + exists (x :: ys). intros z. split; intros H'.
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
        + destruct H as [y H]. exists (y :: ys). intros z. split.
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
