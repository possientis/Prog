Require Import Peano_dec.

Require Import Core.Set.
Require Import Core.Equal.

Definition Env : Type := nat -> set.

Definition envEqual (e e':Env) : Prop := forall (n : nat), e n = e' n.

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

Lemma bindEqual : forall (e:Env) (n m:nat) (x y:set),
    x == y -> bind e n x m == bind e n y m.
Proof.
    intros e n m x y H. destruct (eq_nat_dec n m) as [H'|H'].
    - subst. rewrite bindSame, bindSame. assumption.
    - rewrite bindDiff, bindDiff. apply equalRefl.
        + assumption.
        + assumption.
Qed.

Lemma bindPermute : forall (e:Env) (n m:nat) (x y:set), m <> n -> 
    envEqual (bind (bind e n x) m y) (bind (bind e m y) n x).
Proof.
    intros e n m x y Hmn p. 
    destruct (eq_nat_dec m p) as [H1|H1], (eq_nat_dec n p) as [H2|H2].
    - subst. exfalso. apply Hmn. reflexivity.
    - subst. rewrite bindSame, bindDiff, bindSame.
        + reflexivity.
        + assumption.
    - subst. rewrite bindSame, bindDiff, bindSame.
        + reflexivity.
        + assumption.
    - rewrite bindDiff, bindDiff, bindDiff, bindDiff.
        + reflexivity.
        + assumption.
        + assumption.
        + assumption.
        + assumption.
Qed.

Lemma bindOver : forall (e:Env) (n:nat) (x y:set),
    envEqual (bind (bind e n x) n y) (bind e n y).
Proof.
    intros e n x y m. destruct (eq_nat_dec n m) as [H|H].
    - subst. rewrite bindSame, bindSame. reflexivity.
    - rewrite bindDiff, bindDiff, bindDiff.
        + reflexivity.
        + assumption.
        + assumption.
        + assumption.
Qed.




