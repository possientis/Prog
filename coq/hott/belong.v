Require Import set.
Require Import equal.

Inductive belong : set -> set -> Prop :=
|   Belong : forall (a:Type) (f:a -> set) (x:a), belong (f x) (mkset a f)
|   Compat : forall (x x' y:set), x == x' -> belong x y -> belong x' y
.


Lemma belongR : forall (x y y':set), y == y' -> belong x y -> belong x y'.
Proof.
    intros x y y' E H. induction H. 
        - destruct y' as [b g].
          unfold setEq in E. destruct E as [H1 H2]. destruct (H1 x). subst.
          rewrite H. constructor.
        - apply Compat with x.
            + assumption.
            + apply IHbelong. assumption.
Qed.

