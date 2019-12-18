Require Import Core.Nat.
Require Import Core.Set.
Require Import Core.Elem.
Require Import Core.Formula.


Definition Env : Type := nat -> set.

(* Tweak environment e to that e n = x                                          *)
Definition subst (e:Env) (n:nat) (x:set) : Env :=
    fun (m:nat) =>
        match eq_nat_dec n m with
        | left _    => x        (* variable 'n' is bound to set 'x'             *)
        | right _   => e m
        end.

Fixpoint eval (e:Env) (p:Formula) : Prop :=
    match p with
    | Bot           => False
    | Elem n m      => (e n) :: (e m)
    | Imp p1 p2     => eval e p1 -> eval e p2
    | All n p1      => forall (x:set), eval (subst e n x) p1
    end.



