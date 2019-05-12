
(* Values of type sumor A B are either a value of type A or a proof of B        *) 

(*
Print sumor.

Inductive sumor (A : Type) (B : Prop) : Type :=
    inleft : A -> A + {B} | inright : B -> A + {B}

For inleft, when applied to no more than 1 argument:
Arguments A, B are implicit and maximally inserted
For inleft, when applied to 2 arguments:
Argument A is implicit
For inright, when applied to no more than 1 argument:
Arguments A, B are implicit and maximally inserted
For inright, when applied to 2 arguments:
Argument B is implicit
For sumor: Argument scopes are [type_scope type_scope]
For inleft: Argument scopes are [type_scope type_scope _]
For inright: Argument scopes are [type_scope type_scope _]
*)

(* This is not a 'sumbool' type {A} + {B} but a 'sumor' type A + {B}            *)
Definition pred_strong (n:nat) : {m:nat | S m = n} + {n = 0} :=
    match n with
    | 0     => inright (eq_refl 0)
    | S n   => inleft (exist _ n (eq_refl (S n)))
    end. 
     
(*
Compute pred_strong 5.
    = inleft (exist (fun m : nat => S m = 5) 4 eq_refl)
    : {m : nat | S m = 5} + {5 = 0}
*)

Definition maybe (n:nat) (def:nat) (x:{m:nat | S m = n} + {n = 0}) : nat :=
    match x with
    | inright _             => def
    | inleft (exist _ m _)  => m
    end.

Arguments maybe {n} _ _.

(*
Compute (maybe 0 (pred_strong 10)).
*)

Example pred_strong_test1 : maybe 0 (pred_strong 10) = 9.
Proof. reflexivity. Qed.


Example pred_strong_test2 : maybe 9 (pred_strong 0) = 9.
Proof. reflexivity. Qed.
