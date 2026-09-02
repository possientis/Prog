Require Import set.
Require Import equal.

Inductive belong : set -> set -> Prop :=
|   Belong  : forall (a:Type) (f:a -> set) (x:a), belong (f x) (mkset a f)
|   BelongR : forall (x x' y:set), x == x' -> belong x' y -> belong x y
.


Lemma BelongL: forall (x y' y:set), belong x y' -> y' == y -> belong x y'.
Proof.
    intros x y' y H E. induction H. 
    - constructor.
    - apply BelongR with x'.
        + assumption.
        + apply IHbelong. assumption.
Qed.

Notation "x % y" := (belong x y) (at level 0, no associativity).

(*
Lemma belong_crit : forall (x:set) (a:Type) (f:a -> set),
    x % (mkset a f) -> exists (z:a), x = f z.
Proof.
    intros x a f H. remember (mkset a f) as y eqn:E.
    revert E. revert f. revert a. destruct H.
    - intros b g H. inversion H. subst. exists x. reflexivity.
    -

Show.
*)


