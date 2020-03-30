Require Import List.
Import ListNotations.

Notation "xs <= ys" := (incl xs ys)
    (at level 70, no associativity) : Include_scope.

Open Scope Include_scope.

Lemma incl_cons2 : forall (v:Type) (xs ys:list v) (a:v),
    xs <= ys -> (a :: xs) <= (a :: ys).
Proof.
    intros v xs ys a H. apply incl_cons.
    - left. reflexivity.
    - apply incl_tl. assumption.
Qed.

Lemma incl_app2 : forall (v:Type) (xs xs' ys ys':list v),
    xs <= xs' -> ys <= ys' -> (xs ++ ys) <= (xs' ++ ys').
Proof.
    intros v xs xs' ys ys' H1 H2. apply incl_app.
    - apply incl_appl. assumption.
    - apply incl_appr. assumption.
Qed.


