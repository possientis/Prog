Require Import Core.Set.
Require Import Core.Leq.
Require Import Core.Elem.
Require Import Core.Equal.
Require Import Core.Decidability.

(* Insert the set x inside the set y according to syntactic ordering.           *)
Fixpoint insert (x y:set) : set :=
    match y with
    | Nil           => Cons x Nil
    | (Cons y ys)   =>
        match (leqDec x y) with
        | left _    => Cons y (insert x ys)     (* x 'smaller' goes inside      *)
        | right _   => Cons x (Cons y ys)
        end
    end.

(*
Lemma insertSemantics : forall (x xs:set), 
    (x :: xs) /\ (insert x xs == xs)        \/
   ~(x :: xs) /\ (insert x xs == Cons x xs). 
Proof.
    intros x ys. revert ys x. induction ys as [|y IH1 ys IH2]; intros x.
    - admit.
    - simpl. destruct (leqDec x y) as [H|H].
    

Show.
*)

(*
Lemma insertIn : forall (x xs:set), x :: xs -> insert x xs == xs.
Proof.

Show.
*)

(*
Lemma insertCompatL : forall (x x' y:set), x == x' -> insert x y == insert x' y.
Proof.
    intros x x' y. revert y x x'. induction y as [|y IH1 ys IH2]; intros x x' H.
    - admit.
    - simpl. destruct (leqDec x y) as [H1|H1]; destruct (leqDec x' y) as [H2|H2].
        + admit.
        +

Show.
*)

(*
Lemma insertCompatR : forall (x y y':set), y == y' -> insert x y == insert x y'.
Proof.

Show.
*)

(*
Lemma insertNotIn : forall (x xs:set), ~ x :: xs  -> insert x xs == Cons x xs.
Proof.

Show.
*)

   
