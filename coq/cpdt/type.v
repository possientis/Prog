Require Import Arith.PeanoNat.

Inductive type : Set :=
| Nat  : type
| Bool : type
| Prod : type -> type -> type
.

Inductive exp : type -> Set :=
| NConst : nat -> exp Nat
| Plus   : exp Nat -> exp Nat -> exp Nat
| Eq     : exp Nat -> exp Nat -> exp Bool
| BConst : bool -> exp Bool
| And    : exp Bool -> exp Bool -> exp Bool
| If     : forall (t:type), exp Bool -> exp t -> exp t -> exp t
| Pair   : forall (t1 t2:type), exp t1 -> exp t2 -> exp (Prod t1 t2)
| Fst    : forall (t1 t2:type), exp (Prod t1 t2) -> exp t1
| Snd    : forall (t1 t2:type), exp (Prod t1 t2) -> exp t2
.

Fixpoint typeDenote (t:type) : Set :=
    match t with
    | Nat           => nat
    | Bool          => bool
    | Prod t1 t2    => typeDenote t1 * typeDenote t2
    end. 

(*
Fixpoint expDenote (t :type) (e:exp t) : typeDenote t :=
    match e with
    | NConst n      => n
    | Plus e1 e2    => expDenote Nat e1 + expDenote Nat e2
    | Eq e1 e2      => 
        match eq_dec (expDenote Nat e1) (expDenote Nat e2) with 
        | left  _   => true
        | right _   => false
        end
    end.
*)
