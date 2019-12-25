Require Import Peano_dec.

Require Import Core.Set.

Definition Env : Type := nat -> set.

(* Safe environment allowing variables to be unbound leading to error checking. *)
Definition Env' : Type := nat -> option set.

Definition env0  : Env  := (fun _ => Nil).
Definition env0' : Env' := (fun _ => None).

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

Lemma bindSame : forall (e:Env) (n:nat) (x:set), bind e n x n = x.
Proof. 
    intros e n x. unfold bind. destruct (eq_nat_dec n n) as [H|H].
    - reflexivity.
    - exfalso. apply H. reflexivity.
Qed.

Lemma bindDiff : forall (e:Env) (n m:nat) (x:set), 
    n <> m -> bind e n x m = e m.
Proof.
    intros e n m x H. unfold bind. destruct (eq_nat_dec n m) as [H'|H'].
    - exfalso. apply H. assumption.
    - reflexivity.
Qed.
