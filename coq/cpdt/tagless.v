Set Implicit Arguments.

Require Import Arith.
Require Import Bool.

Inductive type : Set :=
    | Nat   : type
    | Bool  : type
    | Prod  : type -> type -> type
    .

Inductive exp : type    -> Set :=
    | NConst: nat       -> exp Nat
    | Plus  : exp Nat   -> exp Nat  -> exp Nat
    | Eq    : exp Nat   -> exp Nat  -> exp Bool

    | BConst: bool      -> exp Bool
    | And   : exp Bool  -> exp Bool -> exp Bool
    | If    : forall t, exp Bool -> exp t -> exp t -> exp t

    | Pair  : forall t1 t2, exp t1 -> exp t2 -> exp (Prod t1 t2)
    | Fst   : forall t1 t2, exp (Prod t1 t2) -> exp t1
    | Snd   : forall t1 t2, exp (Prod t1 t2) -> exp t2
    .


Fixpoint typeDenote (t:type) : Set :=
    match t with
        | Nat           => nat
        | Bool          => bool
        | Prod t1 t2    => typeDenote t1 * typeDenote t2
    end%type. (* annotation for parsing '*' *)

Compute typeDenote Nat.
Compute typeDenote Bool.
Compute typeDenote (Prod Nat Bool).

Fixpoint expDenote {t:type}(e:exp t) : typeDenote t :=
    match e with
        | NConst n      => n
        | Plus e1 e2    => expDenote e1 + expDenote e2
        | Eq e1 e2      => if eq_nat_dec (expDenote e1) (expDenote e2) 
                               then true else false
        | BConst b      => b
        | And e1 e2     => expDenote e1 && expDenote e2
        | If e' e1 e2   => if expDenote e' then expDenote e1 else expDenote e2

        | Pair e1 e2    => (expDenote e1, expDenote e2)
        | Fst e'        => fst (expDenote e')
        | Snd e'        => snd (expDenote e')
    end.


Definition pairOutType (t:type) := option (
    match t with
        | Prod t1 t2    => exp t1 * exp t2
        | _             => unit
    end
).


Definition pairOut {t:type}(e:exp t) : pairOutType t :=
    match e in (exp t) return (pairOutType t) with
        | Pair e1 e2        => Some (e1,e2)
        | _                 => None
    end.





