Extraction Language Haskell.

(*
Print sumbool.
Inductive sumbool (A B : Prop) : Set :=
    left : A -> {A} + {B} | right : B -> {A} + {B}

For left, when applied to no more than 1 argument:
Arguments A, B are implicit and maximally inserted
For left, when applied to 2 arguments:
Argument A is implicit
For right, when applied to no more than 1 argument:
Arguments A, B are implicit and maximally inserted
For right, when applied to 2 arguments:
Argument B is implicit
For sumbool: Argument scopes are [type_scope type_scope]
For left: Argument scopes are [type_scope type_scope _]
For right: Argument scopes are [type_scope type_scope _]
*)

(*
Check left.   (* : ?A -> {?A} + {?B}                        *)
Check right.  (* : ?B -> {?A} + {?B}                        *)
Check @left.  (* : forall (A B:Prop), A -> {A} + {B}        *)
Check @right. (* : forall (A B:Prop), B -> {A} + {B}        *)
*)


Notation "'Yes'" := (left _).
Notation "'No'"  := (right _).

(* The if form actually works when the test expression has  *)
(* any two-constructor inductive type                       *)

Notation "'Reduce' x" := (if x then Yes else No) (at level 50).


Definition eq_nat_dec : forall (n m:nat), {n = m} + {n <> m}.
Proof. 
    induction n, m.
    - left. reflexivity.
    - right. intros H. inversion H.
    - right. intros H. inversion H.
    - destruct (IHn m) as [H|H]. subst.
        + left. reflexivity.
        + right. intros H'. apply H. inversion H'. reflexivity.
Defined.


(*
Compute (eq_nat_dec 2 3).
Compute (eq_nat_dec 5 5).

Extraction eq_nat_dec.
*)


Definition eq_nat_dec' : forall (n m:nat), {n = m} + {n <> m}.
(* you don't need the word 'Proof' it seems                                     *)
    refine (fix f (n m:nat) : {n = m} + {n <> m} :=
        match n,m with
        | 0,0           => Yes
        | S n', S m'    => Reduce (f n' m')
        | _, _          => No
        end); congruence.
Defined.


