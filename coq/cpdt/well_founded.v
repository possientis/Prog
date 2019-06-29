Require Import List.
Require Import Arith.Le.

Require Import stream.

Fixpoint insert (a:Type) (le:a -> a -> bool) (x:a) (xs:list a) : list a :=
    match xs with
    | nil       => x :: nil
    | (y :: ys) => if le x y
        then x :: xs
        else y :: insert a le x ys
    end.

Arguments insert {a} _ _ _.

Fixpoint merge (a:Type) (le:a -> a -> bool) (xs ys:list a) : list a :=
    match xs with
    | nil       => ys
    | (x :: xs) => insert le x (merge a le xs ys)
    end. 

Arguments merge {a} _ _ _.


Fixpoint split (a:Type) (xs:list a) : list a * list a :=
    match xs with
    | nil           => (nil, nil)
    | x :: nil      => (x :: nil, nil)
    | x :: y :: xs  =>
        let (l1,l2) := split a xs in
            (x :: l1, y :: l2)
    end.

Arguments split {a} _.

(* not apparent that recursion is will-founded                                  *)
Fail Fixpoint mergeSort (a:Type) (le:a -> a -> bool) (xs : list a) : list a :=
    match xs with
    | nil       => nil
    | x :: nil  => x :: nil
    | _         => let (l1, l2) := split xs in
        merge le (mergeSort a le l1) (mergeSort a le l2)
    end.

(* A relation is well-founded iff every point is accessible                     *)

(*
Print well_founded.

fun (A : Type) (R : A -> A -> Prop) => forall a : A, Acc R a
     : forall A : Type, (A -> A -> Prop) -> Prop
*)

(* Accessibility relation                                                       *)

(*
Print Acc.

Inductive Acc (A : Type) (R : A -> A -> Prop) (x : A) : Prop :=
    Acc_intro : (forall y : A, R y x -> Acc R y) -> Acc R x

    For Acc: Argument A is implicit
    For Acc_intro: Arguments A, R are implicit
    For Acc: Argument scopes are [type_scope function_scope _]
    For Acc_intro: Argument scopes are [type_scope function_scope _
                     function_scope]
*)

(* If you have an infinite descending chain starting with y and y happens to be *)
(* less than x, then you have an infinite descending chain starting with x      *)
(* This type needs to be coinductive, it would be void as an inductive type     *)
CoInductive oo_chain (a:Type) (R:a -> a -> Prop) : Stream a -> Prop :=
| oo_Cons : forall (x y:a) (s:Stream a), 
    oo_chain a R (Cons y s) -> R y x -> oo_chain a R (Cons x (Cons y s)).

Arguments oo_chain {a} _ _.

(* The accessible points are minimal elements or points which have nothing      *)
(* underneath but accesible points. So an accessible point cannot start a chain *)
Lemma no_oo_chain : forall (a:Type) (R:a -> a -> Prop) (x:a),
    Acc R x -> forall (s:Stream a), ~oo_chain R (Cons x s).
Proof.
    intros a R x H. induction H as [x H IH]. intros [y s].
    intros H'. revert H IH. 
    remember (Cons x (Cons y s)) as s' eqn:E. revert x y s E.
    destruct H'.
    intros x' y' s' H0. inversion H0. subst.
    rename x' into x. rename y' into y. rename s' into s.
    intros H1 H2. apply (H2 y) with s in H.
    apply H. assumption.
Qed.

(*
Check Fix.
Fix
     : forall (A : Type) (R : A -> A -> Prop),
       well_founded R ->
       forall P : A -> Type,
       (forall x : A, (forall y : A, R y x -> P y) -> P x) ->
       forall x : A, P x
*)

Definition lengthOrder (a:Type) (l1 l2 : list a) : Prop :=
    length l1 < length l2.


Arguments lengthOrder {a} _ _.


Lemma lengthOrder_wf' : forall (a:Type) (n:nat) (l:list a), 
    length l <= n -> Acc lengthOrder l.
Proof.
    intros a. induction n as [|n IH].
    - intros l. destruct l as [|x l].
        +  intros _. constructor. intros l H. inversion H.
        +  intros H. inversion H.
    - intros l H. constructor. intros l' H'. apply IH.
      unfold lengthOrder in H'. unfold lt in H'.
      apply le_S_n. apply le_trans with (length l); assumption.  
Defined. (* not opaque *)

Lemma lengthOrder_wf : forall (a:Type), well_founded (@lengthOrder a). 
Proof.
    intros a. unfold well_founded. intros l. 
    apply lengthOrder_wf' with (length l). 
    apply le_n.
Defined. (* not opaque *)

(*
Lemma split_wf : forall (a:Type) (n:nat) (l:list a),
    2 <= length l <= n -> 
        let (l1,l2) := split l in 
            lengthOrder l1 l /\ lengthOrder l2 l.
Proof.
    intros a n l. revert n. 
    induction l as [|x l IH].
    - intros n [H1 H2]. inversion H1.
    - revert x IH. 
      induction l as [| y l IH'].
        + intros x IH n [H1 H2]. 
          simpl in H1. apply le_S_n in H1. inversion H1. 
        + intros x IH n [H1 H2].
          unfold split. fold (split l).
Show.
*)
