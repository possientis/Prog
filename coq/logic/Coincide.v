Require Import List.

Require Import In.

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
    incl ys xs -> coincide xs f g -> coincide ys f g.
Proof.
    intros v w f g xs ys H H' x H1. apply H in H1. apply H'. assumption.
Qed.


