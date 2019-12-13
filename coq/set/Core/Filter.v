(* NEXT: ===> Decidability                                                      *)


Require Import List.

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
(* list of sets satisfying a given decidable predicate. We first define the     *)
(* notion of decidable predicate: let 'a' be a type and 'p:a -> Prop' be a      *)
(* predicate. Saying that the predicate 'p' is decidable is saying 'Dec p'      *)
(* which we are defining as the 'statement':                                    *)
(*      Dec p := forall (x:a), {p x} + {~p x}                                   *)
(* However, this 'statement' is not a value of type 'Prop'. In other words, it  *)
(* is not a Coq proposition. It is simply a type, namely the type of dependent  *)
(* function q, which given an (x:a) returns a value q x of type {p x} + {~p x}, *)
(* which is either a proof that p x holds, or a proof that ~p x holds.          *)
(* So saying that 'q' is of type 'Dec p', i.e. the jugement 'q:Dec p' is simply *)
(* saying that 'q' is such a dependent function. Informally, we could think of  *)
(* q as 'a proof of Dec p', or a witness to the fact that p is a decidable.     *)
Definition Dec (a:Type) (p:a -> Prop) := forall (x:a), {p x} + {~p x}.

Arguments Dec {a}.

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
Lemma filter_equiv : forall (a:Type) (p:a -> Prop) (q:Dec p) (xs:list a) (x:a),
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
Lemma exists_nil : forall (a:Type) (xs:list a),
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
Lemma filter_nil : forall (a:Type) (p:a -> Prop) (q:Dec p) (xs:list a),
    (exists (x:a), In x xs /\ p x) <-> filter q xs <> nil.
Proof.
    intros a p q xs. split.
    - intros [x H]. apply exists_nil. exists x. apply filter_equiv. assumption.
    - intros H. apply exists_nil in H. destruct H as [x H]. exists x.
      apply (filter_equiv a p q). assumption.
Qed.

Arguments filter_nil {a} {p}.

(* Whether a list is the empty list or not is decidable.                        *)
Lemma nil_dec : forall (a:Type) (xs:list a), {xs = nil} + {xs <> nil}.
Proof.
    intros a xs. destruct xs as [|x xs].
    - left. reflexivity.
    - right. intros H. inversion H.
Qed.


Arguments nil_dec {a}.

(* This is the main result of this module which we shall crucially use in order *)
(* to prove the decidability of set inclusion in our model. Given a decidable   *)
(* predicate p and a list xs, whether or not xs has an element which satisfies  *)
(* the predicate p is a decidable property.                                     *)
Theorem in_pred_dec : forall (a:Type) (p:a -> Prop) (q:Dec p) (xs:list a),
    {exists (x:a), In x xs /\ p x} + {~ exists (x:a), In x xs /\ p x}.
Proof.
    intros a p q xs. destruct (nil_dec (filter q xs)) as [H|H] eqn:E.
    - right. intros H'. apply (filter_nil q) in H'. apply H'. assumption.
    - left. apply (filter_nil q). assumption.
Qed.

