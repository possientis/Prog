Require Import List.
Import ListNotations.

Lemma incl_cons2 : forall (v:Type) (l l':list v) (a:v),
    incl l l' -> incl (a :: l) (a :: l').
Proof.
    intros v l l' a H. apply incl_cons.
    - left. reflexivity.
    - apply incl_tl. assumption.
Qed.

Lemma incl_app2 : forall (v:Type) (xs xs' ys ys':list v),
    incl xs xs' -> incl ys ys' -> incl (xs ++ ys) (xs' ++ ys').
Proof.
    intros v xs xs' ys ys' H1 H2. apply incl_app.
    - apply incl_appl. assumption.
    - apply incl_appr. assumption.
Qed.


