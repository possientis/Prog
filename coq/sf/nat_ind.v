Require Import nat.

Fixpoint nat_ind' (n:nat): forall (P:nat -> Prop),
    P 0 -> (forall n, P n -> P (S n)) -> P n :=
    fun (P:nat -> Prop) =>
        fun (H0 : P 0)  =>
            fun (IH : forall n, P n -> P (S n)) =>
                match n as m return P m with
                | 0     => H0
                | S p   => IH p (nat_ind' p P H0 IH)
                end. 
(*
Definition nat_ind : forall (P:nat -> Prop),
    P 0 -> (forall n, P n -> P (S n)) -> forall n, P n :=
    fun P H0 IH n => nat_ind' n P H0 IH.
*)

(*
Print nat_ind.
*)





  




