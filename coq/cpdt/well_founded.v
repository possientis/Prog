Require Import List.

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
(*
Print well_founded.
*)

(*
fun (A : Type) (R : A -> A -> Prop) => forall a : A, Acc R a
     : forall A : Type, (A -> A -> Prop) -> Prop
*)

(* Accessibility relation                                                       *)

(*
Print Acc.
*)

(*
Inductive Acc (A : Type) (R : A -> A -> Prop) (x : A) : Prop :=
    Acc_intro : (forall y : A, R y x -> Acc R y) -> Acc R x

    For Acc: Argument A is implicit
    For Acc_intro: Arguments A, R are implicit
    For Acc: Argument scopes are [type_scope function_scope _]
    For Acc_intro: Argument scopes are [type_scope function_scope _
                     function_scope]
*)

CoInductive oo_chain (a:Type) (R:a -> a -> Prop) : Stream a -> Prop :=
| oo_Cons : forall (x y:a) (s:Stream a), 
    oo_chain a R (Cons y s) -> R y x -> oo_chain a R (Cons x (Cons y s)).

Arguments oo_chain {a} _ _.

(* If x is accessible, it cannot be the start of an infinite descending chain.  *)
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


