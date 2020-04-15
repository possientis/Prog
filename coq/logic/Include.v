Require Import List.

Notation "xs <= ys" := (incl xs ys)
    (at level 70, no associativity) : Include_scope.

Open Scope Include_scope.

Lemma incl_cons2 : forall (v:Type) (xs ys:list v) (a:v),
    xs <= ys -> (cons a xs) <= (cons a ys).
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

Lemma incl_map : forall (v w:Type) (f:v -> w) (xs ys:list v),
    xs <= ys -> map f xs <= map f ys.
Proof.
    intros v w f xs ys H1 z H2. rewrite in_map_iff in H2. 
    destruct H2 as [x [H2 H3]]. apply in_map_iff. exists x. split.
    - assumption.
    - apply H1. assumption.
Qed.

(*
Lemma incl_concat : forall (v:Type) (xss yss:list (list v)),
    xss <= yss -> concat xss <= concat yss.
Show.

Proof.
*)
