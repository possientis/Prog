Require Import List.
Import ListNotations.

Lemma incl_app2 : forall (v:Type) (l1 l1' l2 l2':list v),
    incl l1 l1' -> incl l2 l2' -> incl (l1 ++ l2) (l1' ++ l2').
Proof.
    intros v l1 l1' l2 l2' H1 H2. apply incl_app.
    - apply incl_appl. assumption.
    - apply incl_appr. assumption.
Qed.

Lemma incl_cons2 : forall (v:Type) (l l':list v) (a:v),
    incl l l' -> incl (a :: l) (a :: l').
Proof.
    intros v l l' a H. apply incl_cons.
    - left. reflexivity.
    - apply incl_tl. assumption.
Qed.


Lemma incl_map : forall (v w:Type) (f:v -> w) (l:list v) (x:v),
    In x l -> In (f x) (map f l).
Proof.
    intros v w f l. induction l as [|a l IH]; intros x.
    - intros H. inversion H.
    - intros [H|H]; simpl.
        + left. rewrite H. reflexivity.
        + right. apply IH. assumption.
Qed.





