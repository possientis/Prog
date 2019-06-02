Require Import List.

Require Import Fol.P.

(* We do not have sets: the variables of a formula are a list, not a set.       *)

Fixpoint var (v:Type) (p:P v) : list v :=
    match p with
    | Bot       => nil
    | Elem x y  => cons x (cons y nil)
    | Imp p1 p2 => var v p1 ++ var v p2
    | All x p1  => cons x (var v p1)
    end.

Arguments var {v} _.


Lemma var_fmap : forall (v w:Type) (f:v -> w) (p:P v),
    var (fmap f p) = map f (var p).
Proof.
    intros v w f.
    induction p as [|x y|p1 IH1 p2 IH2|x p1 IH1]; simpl.
    - reflexivity.
    - reflexivity.
    - rewrite map_app, IH1, IH2. reflexivity.
    - rewrite IH1. reflexivity.
Qed.

(* If two functions f g coincide on the variables of a formula p, then the      *)
(* formulas fmap f t and fmap g t are equal, and conversely.                    *)
Lemma var_support : forall (v w:Type) (f g:v -> w) (p:P v),
    (forall (x:v), In x (var p) -> f x = g x) <-> fmap f p = fmap g p.
Proof.
    intros v w f g. 
    induction p as [|x y|p1 [IH1 IH1'] p2 [IH2 IH2']|x p1 [IH1 IH1']]; 
    simpl; split.
    - intros. reflexivity.
    - intros. exfalso. assumption.
    - intros H. rewrite (H x), (H y).
        + reflexivity.
        + right. left. reflexivity.
        + left. reflexivity.
    - intros H. inversion H. intros z [H'|[H'|H']].
        + subst. assumption.
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
 
