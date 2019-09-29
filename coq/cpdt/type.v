Require Import Arith.PeanoNat.

Require Import Utils.nat.

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


Fixpoint expDenote (t :type) (e:exp t) : typeDenote t :=
    match e with
    | NConst n      => n
    | Plus e1 e2    => expDenote Nat e1 + expDenote Nat e2
    | Eq e1 e2      => 
        match nat_dec (expDenote Nat e1) (expDenote Nat e2) with 
        | left  _   => true
        | right _   => false
        end
    | BConst b      => b
    | And b1 b2     => if (expDenote Bool b1)
        then (expDenote Bool b2)
        else false
    | If _ b e1 e2    => if (expDenote Bool b) 
        then expDenote _ e1 
        else expDenote _ e2 
    | Pair _ _ e1 e2  => (expDenote _ e1, expDenote _ e2)
    | Fst _ _ e       => fst (expDenote _ e)
    | Snd _ _ e       => snd (expDenote _ e)
    end.

Definition pairOutType (t:type) := option (
    match t with
    | Prod t1 t2 => exp t1 * exp t2
    | _          => unit
    end).


Definition pairOut (t:type) (e:exp t) : pairOutType t :=
    match e in (exp t) return pairOutType t with
    | Pair _ _ e1 e2 => Some (e1,e2)
    | _              => None
    end.



