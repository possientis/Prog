Require Import bool.
Require Import list.
Require Import In.
Require Import higher_order.

(* merge k m l  == 'l is an in order merge of k and m' *)
Inductive merge (a:Type) : list a -> list a -> list a -> Prop :=
| merge_nil_l  : forall (l:list a), merge a [] l l
| merge_nil_r  : forall (l:list a), merge a l [] l
| merge_cons_l : forall (k m l: list a) (x:a), 
    merge a k m l -> merge a (x :: k) m (x :: l)
| merge_cons_r : forall (k m l:list a) (x:a),
    merge a k m l -> merge a k (x :: m) (x :: l) 
.

Arguments merge {a} _ _ _.

(*
Theorem filter_merge : forall (a:Type) (test:a -> bool) (k m l:list a),
    (forall x, In x k -> test x = true) ->
    (forall x, In x m -> test x = false) ->
    merge k m l -> 
    filter test l = k.
Proof.
    intros a test k m l Hk Hm H. revert Hk Hm.
    induction H as [l|l|k m l x H IH|k m l x H IH].
    - intros H0 H. clear H0. apply filter_false. exact H.
    - intros H H0. clear H0. apply filter_true. exact H.
    - intros H1 H2. assert (test x = true) as Hx. { apply H1. left. reflexivity. }
        simpl. rewrite Hx. assert (filter test l = k) as H0.
            { apply IH.
                + intros y H'. apply H1. right. exact H'.
                + exact H2.
            }
        rewrite H0. reflexivity.
    -
    
Show.
*)
