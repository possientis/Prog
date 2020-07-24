Require Import List.

Require Import Logic.List.In.
Require Import Logic.List.Concat.

Notation "xs <= ys" := (incl xs ys)
    (at level 70, no associativity) : Include_scope.

Open Scope Include_scope.

Lemma incl_cons2 : forall (v:Type) (xs ys:list v) (x:v),
    xs <= ys -> (cons x xs) <= (cons x ys).
Proof.
    intros v xs ys x H. apply incl_cons.
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

Lemma incl_concat : forall (v:Type) (xss yss:list (list v)),
    xss <= yss -> concat xss <= concat yss.
Proof.
    intros v xss yss H1 x H2. apply concat_charac.
    rewrite concat_charac in H2. destruct H2 as [xs [H2 H3]].
    exists xs. split.
    - assumption.
    - apply H1. assumption.
Qed.

Lemma incl_concat_map : forall (v:Type) (f:v -> list v) (xs:list v) (x:v),
    x :: xs -> f x <= concat (map f xs).
Proof.
    intros v f xs x H1 y H2. apply concat_charac. exists (f x). split.
    - assumption.
    - apply in_map_iff. exists x. split.
        + reflexivity.
        + assumption. 
Qed.

Lemma incl_nil : forall (v:Type) (xs:list v),
    xs <= nil -> xs = nil.
Proof.
    intros v xs H1. destruct xs as [|x xs].
    - reflexivity.
    - exfalso. assert (x :: nil) as H2.
        { apply H1 with x. left. reflexivity. }
      inversion H2.
Qed.
