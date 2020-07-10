Require Import List.
Require Import Lang1.Syntax.

(* The substitution f is valid, i.e. does not give rise to variable capture.    *)
Inductive Valid (f:nat -> nat) : Formula -> Prop :=
| VBot  : Valid f Bot
| VElem : forall (n m:nat), Valid f (Elem n m)
| VImp  : forall (p q:Formula), Valid f p -> Valid f q -> Valid f (Imp p q)
| VAll  : forall (n:nat) (p:Formula), Valid f p           -> 
    (forall (m:nat), In m (free (All n p)) -> f n <> f m) ->
        Valid f (All n p) 
.

Lemma ValidImp : forall (f:nat -> nat) (p1 p2:Formula), 
    Valid f (Imp p1 p2) -> Valid f p1 /\ Valid f p2.
Proof.
    intros f p1 p2 H1. remember (Imp p1 p2) as p eqn:P. revert p1 p2 P. 
    destruct H1 as [|x y|p1 p2 H1 H2|n p1 H1 H2]; intros q1 q2 H; inversion H.
    - subst. split; assumption.
Qed.


Lemma ValidAll : forall (f:nat -> nat) (n:nat) (p1:Formula),
    Valid f (All n p1) -> Valid f p1 /\
        forall (m:nat), In m (free (All n p1)) -> f n <> f m.
Proof.
    intros f n p1 H1. remember (All n p1) as p eqn:P. revert n p1 P.
    destruct H1 as [|x y|p1 p2 H1 H2|n p1 H1 H2]; intros m q1 H; inversion H.
    - subst. split; assumption.
Qed.

