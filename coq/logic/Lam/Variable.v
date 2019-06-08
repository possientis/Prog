Require Import List.

Require Import Coincide.
Require Import Lam.T.

(* We do not have sets: the variables of a term are a list, not a set.          *)

Fixpoint var (v:Type) (t:T v) : list v :=
    match t with
    | Var x     => cons x nil
    | App t1 t2 => var v t1 ++ var v t2
    | Lam x t1  => cons x  (var v t1)
    end.

Arguments var {v} _.


Lemma var_fmap : forall (v w:Type) (f:v -> w) (t:T v),
    var (fmap f t) = map f (var t).
Proof.
    intros v w f.
    induction t as [x|t1 IH1 t2 IH2|x t1 IH1]; simpl.
    - reflexivity.
    - rewrite map_app, IH1, IH2. reflexivity.
    - rewrite IH1. reflexivity.
Qed.

(* If two functions f g coincide on the variables of a term t, then the terms   *)
(* fmap f t and fmap g t are equal, and conversely.                             *)
Lemma var_support : forall (v w:Type) (f g:v -> w) (t:T v),
    coincide (var t) f g  <-> fmap f t = fmap g t.
Proof.
    intros v w f g. unfold coincide. 
    induction t as [x|t1 [IH1 IH1'] t2 [IH2 IH2']|x t1 [IH1 IH1']]; simpl; split.
    - intros H. rewrite H.
        + reflexivity.
        + left. reflexivity.
    - intros H. inversion H as [H']. clear H. intros y [H|H].
        + subst. assumption.
        + exfalso. assumption.
    - intros H. rewrite IH1, IH2.
        + reflexivity.
        + intros x H'. apply H. apply in_or_app. right. assumption.
        + intros x H'. apply H. apply in_or_app. left.  assumption.
    - intros H. inversion H. intros x H'. apply in_app_or in H'.
      destruct H' as [H'|H']. 
        + apply IH1'; assumption.
        + apply IH2'; assumption.
    - intros H. rewrite IH1.
        + rewrite (H x). { reflexivity. } { left. reflexivity. }
        + intros y H'.  apply H. right. assumption.
    - intros H. inversion H. intros y [H'|H'].
        + subst. assumption.
        + apply IH1'; assumption.
Qed.
