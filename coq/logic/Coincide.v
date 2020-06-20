Require Import List.

Require Import In.
Require Import Include.

(* It is not convenient in Coq to define the notion of the restriction of a     *)
(* function. However, we often need to express the fact that two functions      *)
(* coincide on a given subset. This we can do using a list instead of subset    *) 
Definition coincide (v w:Type) (xs:list v) (f g:v -> w) : Prop :=
    (forall (x:v), x :: xs -> f x = g x).

Arguments coincide {v} {w} _ _ _.


Lemma coincide_map : forall (v w:Type) (f g:v -> w) (xs:list v),
    coincide xs f g -> map f xs = map g xs.
Proof.
    intros v w f g. induction xs as [|x xs IH]. 
    - intros. reflexivity.
    - intros H. simpl. unfold coincide in H.
      rewrite (H x). rewrite IH.
        + reflexivity.
        + unfold coincide. intros u Hu. apply H. right. assumption.
        + left. reflexivity.
Qed.

Lemma coincide_incl : forall (v w:Type) (f g:v -> w) (xs ys:list v),
    ys <= xs -> coincide xs f g -> coincide ys f g.
Proof.
    intros v w f g xs ys H H' x H1. apply H in H1. apply H'. assumption.
Qed.

Lemma coincide_cons : forall (v w:Type) (f g:v -> w) (x:v) (xs:list v),
    coincide (cons x xs) f g -> coincide xs f g.
Proof.
    intros v w f g x xs H z H'. apply H. right. assumption.
Qed.

Lemma coincide_app : forall (v w:Type) (f g:v -> w) (xs ys:list v),
    coincide xs f g -> coincide ys f g -> coincide (xs ++ ys) f g.
Proof.
    intros v w f g. induction xs as [|x xs IH]; intros ys H1 H2; simpl.
    - assumption.
    - unfold coincide. intros z [H3|H3].
        + subst. apply H1. left. reflexivity.
        + apply (IH ys). 
            { apply coincide_cons with x. assumption. }
            { assumption. }
            { assumption. }
Qed.

Lemma coincide_app' : forall (v w:Type) (f g:v -> w) (xs ys:list v),
    coincide (xs ++ ys) f g -> coincide xs f g /\ coincide ys f g.
Proof.
    intros v w f g. destruct xs as [|x xs]; intros ys H1; unfold coincide.
    - split; intros x H2.
        + simpl in H2. contradiction.
        + simpl in H1. apply H1. assumption.
    - split; intros y.
        + intros [H2|H2].
            { subst. apply H1. left. reflexivity. }
            { apply H1. right. apply in_or_app. left. assumption. }
        + intros H2. apply H1. right. apply in_or_app. right. assumption.
Qed.



