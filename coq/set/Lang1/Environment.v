Require Import List.
Require Import Peano_dec.

Require Import Utils.Replace.
Require Import Utils.Composition.

Require Import Core.Set.
Require Import Core.Equal.

Require Import Lang1.Syntax.

Definition Env : Type := nat -> set.

Definition envEqual (e e':Env) : Prop := forall (n:nat), e n == e' n. 

Lemma envEqualRefl : forall (e:Env), envEqual e e.
Proof.
    unfold envEqual. intros e n. apply equalRefl.
Qed.

Lemma envEqualSym : forall (e e':Env), envEqual e e' -> envEqual e' e.
Proof.
    unfold envEqual. intros e e' H n. apply equalSym. apply H.
Qed.

Lemma envEqualTrans : forall (e1 e2 e3:Env), 
    envEqual e1 e2 -> envEqual e2 e3 -> envEqual e1 e3.
Proof.
    unfold envEqual. intros e1 e2 e3 H1 H2 n. apply equalTrans with (e2 n).
    - apply H1.
    - apply H2.
Qed.

(* Tweak environment e so that e n = x                                          *)
Definition bind (e:Env) (n:nat) (x:set) : Env :=
    fun (m:nat) =>
        match eq_nat_dec n m with
        | left _    => x        (* variable 'n' is bound to set 'x'             *)
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
        + apply equalRefl.
        + assumption.
    - subst. rewrite bindSame, bindDiff, bindSame.
        + apply equalRefl.
        + assumption.
    - rewrite bindDiff, bindDiff, bindDiff, bindDiff.
        + apply equalRefl.
        + assumption.
        + assumption.
        + assumption.
        + assumption.
Qed.

Lemma bindOver : forall (e:Env) (n:nat) (x y:set),
    envEqual (bind (bind e n x) n y) (bind e n y).
Proof.
    intros e n x y m. destruct (eq_nat_dec n m) as [H|H].
    - subst. rewrite bindSame, bindSame. apply equalRefl.
    - rewrite bindDiff, bindDiff, bindDiff.
        + apply equalRefl.
        + assumption.
        + assumption.
        + assumption.
Qed.


Lemma bindEnvEqual : forall (e e':Env) (n:nat) (x x':set),
    envEqual e e' -> x == x' -> envEqual (bind e n x) (bind e' n x').
Proof.
    intros e e' n x x'. unfold envEqual. intros H1 H2 m. 
    destruct (eq_nat_dec n m) as [H3|H3]. 
    - subst. rewrite bindSame, bindSame. assumption.
    - rewrite bindDiff, bindDiff. apply H1.
        + assumption.
        + assumption.
Qed.


Lemma bindReplace : forall (e:Env) (n m p:nat) (x:set),
    n <> p -> (bind e n x ; replace m n) p == bind e m x p.
Proof.
    intros e n m p x H. unfold bind, replace, comp. 
    destruct (eq_nat_dec p m) as [H1|H1].
    - subst. 
      destruct (eq_nat_dec n n) as [H2|H2]; 
      destruct (eq_nat_dec m m) as [H3|H3].
        + apply equalRefl.
        + exfalso. apply H3. reflexivity.
        + exfalso. apply H2. reflexivity.
        + exfalso. apply H2. reflexivity.
    - destruct (eq_nat_dec n p) as [H2|H2];
      destruct (eq_nat_dec m p) as [H3|H3].
        + apply equalRefl.
        + exfalso. apply H. assumption.
        + exfalso. subst. apply H1. reflexivity.
        + apply equalRefl.
Qed.

