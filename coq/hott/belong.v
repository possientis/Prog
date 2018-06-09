Require Import set.
Require Import equal.

Inductive belong : set -> set -> Prop :=
|   Belong : forall (a:Type) (f:a -> set) (x:a), belong (f x) (mkset a f)
.


Lemma belongR : forall (x y y':set), y == y' -> belong x y -> belong x y'.
Proof.
    intros x y y' E H. induction H. 
        - destruct y' as [b g].
          unfold setEq in E. destruct E as [H1 H2]. destruct (H1 x). subst.
          rewrite H. constructor.
Qed.

Notation "x % y" := (belong x y) (at level 0, no associativity).


Lemma belong_crit : forall (x:set) (a:Type) (f:a -> set),
    x % (mkset a f) -> exists (z:a), x = f z.
Proof.
    intros x a f H. remember (mkset a f) as y eqn:E.
    revert E. revert f. revert a. destruct H.
    intros b g H. inversion H. subst. exists x. reflexivity.
Qed.



