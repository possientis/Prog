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

Arguments expDenote {t}.

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

Arguments pairOut {t}.

Fixpoint cfold (t:type) (e:exp t) : exp t :=
    match e with
    | NConst n      => NConst n
    | Plus e1 e2    =>
        let e1' := cfold Nat e1 in
        let e2' := cfold Nat e2 in
        match e1', e2' with
        | NConst n1, NConst n2  => NConst (n1 + n2)
        | _        , _          => Plus e1' e2'
        end
    | Eq e1 e2      =>
        let e1' := cfold Nat e1 in
        let e2' := cfold Nat e2 in
        match e1', e2' with
        | NConst n1, NConst n2  => BConst
            match nat_dec n1 n2 with
            | left  _   => true
            | right _   => false
            end 
        | _        , _          => Eq e1' e2'
        end
    | BConst b      => BConst b
    | And e1 e2     =>
        let e1' := cfold Bool e1 in
        let e2' := cfold Bool e2 in
        match e1', e2' with
        | BConst b1, BConst b2  => BConst (b1 && b2)
        | _        , _          => And e1' e2'
        end
    | If _ e e1 e2  =>
        let e' := cfold Bool e in
        match e' with
        | BConst true   => cfold _ e1
        | BConst false  => cfold _ e2
        | _             => If _ e' (cfold _ e1) (cfold _ e2)
        end 
    | Pair _ _ e1 e2 => Pair _ _ (cfold _ e1) (cfold _ e2)
    | Fst _ _ e     => 
        let e' := cfold _ e in
        match pairOut e' with
        | Some p        => fst p
        | None          => Fst _ _ e'
        end
    | Snd _ _ e     => 
        let e' := cfold _ e in
        match pairOut e' with
        | Some p        => snd p
        | None          => Snd _ _ e'
        end
    end.

Arguments cfold {t}.

(* book is useless *)
(*
Theorem cfold_correct : forall (t:type) (e:exp t), expDenote e = expDenote (cfold e).
Proof.
    intros t. induction e as [n|e1 IH1 e2 IH2| | | | | | | ].
    - reflexivity.
    - simpl. remember (cfold e1) as f1 eqn:E1. remember (cfold e2) as f2 eqn:E2.
      revert E1 E2 IH1 IH2.

Show.
*)


