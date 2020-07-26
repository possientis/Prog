Require Import List.

Require Import Logic.Nat.Eq.
Require Import Logic.Class.Eq.
Require Import Logic.Func.Replace.

Require Import Logic.Set.Set.
Require Import Logic.Set.Equal.

Require Import Logic.Lang1.Syntax.

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
        match eqDec n m with
        | left _    => x        (* variable 'n' is bound to set 'x'             *)
        | right _   => e m
        end.

Lemma bindSame : forall (e:Env) (n:nat) (x:set), bind e n x n = x.
Proof. 
    intros e n x. unfold bind. destruct (eqDec n n) as [H|H].
    - reflexivity.
    - exfalso. apply H. reflexivity.
Qed.

Lemma bindDiff : forall (e:Env) (n m:nat) (x:set), 
    n <> m -> bind e n x m = e m.
Proof.
    intros e n m x H. unfold bind. destruct (eqDec n m) as [H'|H'].
    - exfalso. apply H. assumption.
    - reflexivity.
Qed.

Lemma bindEqual : forall (e:Env) (n m:nat) (x y:set),
    x == y -> bind e n x m == bind e n y m.
Proof.
    intros e n m x y H. destruct (eqDec n m) as [H'|H'].
    - subst. rewrite bindSame, bindSame. assumption.
    - rewrite bindDiff, bindDiff. apply equalRefl.
        + assumption.
        + assumption.
Qed.

Lemma bindPermute : forall (e:Env) (n m:nat) (x y:set), m <> n -> 
    envEqual (bind (bind e n x) m y) (bind (bind e m y) n x).
Proof.
    intros e n m x y Hmn p.
    destruct (eqDec m p) as [H1|H1], (eqDec n p) as [H2|H2].
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
    intros e n x y m. destruct (eqDec n m) as [H|H].
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
    destruct (eqDec n m) as [H3|H3]. 
    - subst. rewrite bindSame, bindSame. assumption.
    - rewrite bindDiff, bindDiff. apply H1.
        + assumption.
        + assumption.
Qed.


Lemma bindReplace : forall (e:Env) (n n' k:nat) (x:set),
    n' <> k -> bind e n' x (replace n n' k) == bind e n x k.
Proof.
    intros e n n' k x H. unfold bind, replace. 
    destruct (eqDec k n) as [H1|H1].
    - subst. 
      destruct (eqDec n' n') as [H2|H2]; 
      destruct (eqDec n n) as [H3|H3].
        + apply equalRefl.
        + exfalso. apply H3. reflexivity.
        + exfalso. apply H2. reflexivity.
        + exfalso. apply H2. reflexivity.
    - destruct (eqDec n' k) as [H2|H2];
      destruct (eqDec n k) as [H3|H3].
        + apply equalRefl.
        + exfalso. apply H. assumption.
        + exfalso. subst. apply H1. reflexivity.
        + apply equalRefl.
Qed.


Lemma bindReplace2 : forall (e:Env) (n m n' m' k:nat) (x y:set),  
 n <> m  -> 
 n' <> m'-> 
 n' <> k ->
 m' <> k ->
    bind (bind e n' x) m' y (replace2 n m n' m' k) == bind (bind e n x) m y k.
Proof.
    intros e n m n' m' k x y H1 H2 H3 H4. unfold bind, replace2.
    destruct (eqDec k n) as [H5|H5].
    - subst. destruct (eqDec m' n') as [H5|H5].
        + subst. exfalso. apply H2. reflexivity.                (* <- H2 *)
        + destruct (eqDec n' n') as [H6|H6].
            { destruct (eqDec m n) as [H7|H7].
                { subst. exfalso. apply H1. reflexivity. }      (* <- H1 *)
                { destruct (eqDec n n) as [H8|H8].
                    { apply equalRefl. }
                    { exfalso. apply H8. reflexivity. }}}
            { exfalso. apply H6. reflexivity. }
    - destruct (eqDec k m) as [H6|H6]. 
        + subst. destruct (eqDec m' m') as [H6|H6].
            { destruct (eqDec m m) as [H7|H7].
                { apply equalRefl. }
                { exfalso.  apply H7. reflexivity. }}
            { exfalso. apply H6. reflexivity. }
        + destruct (eqDec m' k) as [H7|H7].
            { subst. exfalso. apply H4. reflexivity. }          (* <- H4 *)
            { destruct (eqDec n' k) as [H8|H8]. 
                { subst. exfalso. apply H3. reflexivity. }      (* <- H3 *)
                { destruct (eqDec m k) as [H9|H9]. 
                    { subst. exfalso. apply H6. reflexivity. }
                    { destruct (eqDec n k) as [H10|H10].
                        { subst. exfalso. apply H5. reflexivity. }
                        { apply equalRefl. }}}}
Qed.

