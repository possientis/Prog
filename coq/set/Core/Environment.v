Require Import Core.Nat.
Require Import Core.Set.

Definition Env : Type := nat -> set.

(* Safe environment allowing variables to be unbound leading to error checking. *)
Definition Env' : Type := nat -> option set.

Definition eDef  : Env  := (fun _ => Nil).
Definition eDef' : Env' := (fun _ => None).

(* Tweak environment e to that e n = x                                          *)
Definition bind (e:Env) (n:nat) (x:set) : Env :=
    fun (m:nat) =>
        match eq_nat_dec n m with
        | left _    => x        (* variable 'n' is bound to set 'x'             *)
        | right _   => e m
        end.

(* Tweak environment e to that e n = x                                          *)
Definition bind' (e:Env') (n:nat) (x:set) : Env' :=
    fun (m:nat) =>
        match eq_nat_dec n m with
        | left _    => Some x   (* variable 'n' is bound to set 'x'             *)
        | right _   => e m
        end.

(* Environment with single binding n := x, variable 'n' is bound to set 'x'.    *)
Definition env (n:nat) (x:set) : Env := bind eDef n x.
