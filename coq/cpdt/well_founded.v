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

CoInductive infiniteDecreasingChain (a:Type) (R:a -> a -> Prop) : 
    Stream a -> Prop :=
| ChainCons : forall (x y:a) (s:Stream a)
            , infiniteDecreasingChain a R (Cons y s) 
           -> R y x 
           -> infiniteDecreasingChain a R (Cons x (Cons y s)).

Arguments infiniteDecreasingChain {a} _ _.

(*
Lemma noBadChain : forall (a:Type) (R:a -> a -> Prop) (x:a),
    Acc R x -> forall (s:Stream a), ~infiniteDecreasingChain R (Cons x s).
Proof.

Show.
*)

