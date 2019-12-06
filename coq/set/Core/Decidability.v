(* NEXT: ===> Pairing                                                           *) 


Require Import List.

Require Import Core.Set.
Require Import Core.Order.
Require Import Core.Core.
Require Import Core.Incl.
Require Import Core.Elem.
Require Import Core.Equal.
Require Import Core.Filter.
Require Import Core.Extensionality.

(* In this module, we are having a small interlude focussing on decidability    *)
(* results which are specific to the Coq meta-theory, and are not set theoretic *)
(* results. These results are interesting in their own rights, but will also    *)
(* prove useful when attempting to establish some set theoretic properties of   *)
(* our model. By default, the Coq logical system does not allow us to assume    *)
(* the 'law of excluded middle' aka 'LEM'. We could postulate LEM as an axiom   *)
(* of our meta-theory (which is known to be consistent with Coq's logic) but    *)
(* we should remember that our model is just a simple model of finite sets in   *)
(* which many things can be proven without using LEM. For those not so familiar *)
(* with Coq, the term 'forall (x y:set), {x = y} + {x <> y}' is not strictly    *)
(* speaking a 'proposition'. It is a term of type 'Set' and not of type 'Prop'. *)
(* The term 'forall (x y:set), (x = y) \/ (x <> y)' *is* a proposition but is   *)
(* not what we are aiming to 'prove' in the following lemma. Instead, what we   *)
(* are presenting as a 'lemma' is a dependent function with return type equal   *)
(* to 'forall (x y:set), {x = y} + {x <> y}'. Given x y of type 'set' (not to   *)
(* be confused with the Coq type 'Set'), the term 'set_eq_dec x y' is of type   *)
(* '{x = y} + {x <> y}' which corresponds to the Haskell sum type 'Either a b'  *)
(* giving us either a proof of 'x = y' or a proof of 'x <> y'. Hence we are     *)
(* proving the existence of a function which given two sets as arguments, gives *)
(* us back either a proof of their equality or a proof of their non-equality.   *)
(* This is a stonger 'property' than the proposition '(x = y) \/ (x <> y)'      *)
(* which does not tell us which of 'x = y' or 'x <> y' is the case.             *)
Lemma set_eq_dec : forall (x y:set), {x = y} + {x <> y}.
Proof.
    intros xs. induction xs as [|x IH1 xs IH2]; intros ys.
    - destruct ys as [|y ys].
        + left. reflexivity.
        + right. intros H. inversion H.
    - destruct ys as [|y ys].
        + right. intros H. inversion H.
        + destruct (IH1 y) as [H1|H1].
            { subst. destruct (IH2 ys) as [H2|H2].
                { subst. left. reflexivity. }
                { right. intros H. inversion H. apply H2. assumption. }}
            { right. intros H. inversion H. apply H1. assumption. }
Qed.

(* A dependent function which given a 'nat' n and two sets xs ys as arguments,  *)
(* returns either a proof of the (level n) inclusion 'incl_n n xs ys', or a     *)
(* a proof that this inclusion is False. In other words, the partial inclusion  *)
(* statement 'incl_n n xs ys' is said to be 'decidable'.                        *)
Lemma incl_n_dec : forall (n:nat) (xs ys:set), 
    { incl_n n xs ys } + { ~ incl_n n xs ys }.
Proof.
    induction n as [|n IH].
    - intros xs ys. left. apply I.
    - intros xs ys. destruct xs as [|x xs].
        + left. apply I.
        + destruct (IH xs ys) as [H|H].
            { simpl. 
              remember (fun y => incl_n n x y /\ incl_n n y x) as p eqn:P.
              assert (Dec p) as q.
                { unfold Dec. intros y. 
                  destruct (IH x y) as [H1|H1]; destruct (IH y x) as [H2|H2].
                    { left. rewrite P. split; assumption. }
                    { right. rewrite P. intros [H3 H4]. apply H2. assumption. }
                    { right. rewrite P. intros [H3 H4]. apply H1. assumption. }
                    { right. rewrite P. intros [H3 H4]. apply H1. assumption. }}
                  destruct (in_pred_dec _ p q (toList ys)) as [H'|H'].
                        { left. split.
                            { assumption. }
                            { rewrite P in H'. assumption. }}
                        { right. intros [H1 H2]. apply H'. 
                          rewrite P. assumption. }}
            { simpl. right. intros [H1 H2]. apply H. assumption. }
Qed.

(* For all sets x y, the inclusion statement 'x <== y' is decidable.            *)
Lemma incl_dec : forall (x y:set), { x <== y } + { ~ (x <== y) }.
Proof.
    intros x y. unfold incl. apply incl_n_dec.
Qed.

(* For all sets x y, the membership statement 'x :: y' is decidable.            *)             
Lemma elem_dec : forall (x y:set), { x :: y } + { ~ x :: y }.
Proof.
    intros x y. unfold elem. apply incl_dec.
Qed.

(* For all sets x y, the equality statement 'x == y' is decidable.              *)
Lemma equal_dec : forall (x y:set), { x == y } + { ~ (x == y) }.
Proof.
    intros x y.  
    destruct (incl_dec x y) as [H1|H1]; destruct (incl_dec y x) as [H2|H2].
    - left. apply doubleIncl. split; assumption.
    - right. rewrite doubleIncl. intros [H3 H4]. apply H2. assumption.
    - right. rewrite doubleIncl. intros [H3 H4]. apply H1. assumption.
    - right. rewrite doubleIncl. intros [H3 H4]. apply H1. assumption.
Qed.
