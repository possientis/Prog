Require Import list.
Require Import nat.
Require Import bool.


Theorem silly1 : forall (n m o p:nat),
    n = m -> [n,o] = [n,p] -> [n,o] = [m,p].
Proof.
    intros n m o p H1 H2. rewrite <- H1. exact H2.
Qed.


Theorem silly2 : forall (n m o p:nat),
    n = m -> (forall (q r:nat), q = r -> [q,o] = [r,p]) -> [n,o] = [m,p].
Proof.
    intros n m o p H1 H2. apply H2. exact H1.
Qed.


Theorem silly_ex : (forall n:nat, evenb n = true -> oddb (S n) = true) ->
    evenb 3 = true -> oddb 4 = true.
Proof. intros H1 H2. apply H1. exact H2. Qed.


Theorem silly3 : forall n:nat,
    true = eqb n 5 -> eqb (S (S n)) 7 = true.
Proof.
    intros n H. simpl. symmetry. exact H.
Qed.

(*
SearchAbout rev.
*)

Theorem rev_ex1 : forall (a:Type) (l k:list a),
    l = rev k -> k = rev l.
Proof.
    intros a l k H. assert (rev l = rev (rev k)) as H'. { rewrite H. reflexivity. }
    rewrite rev_involutive in H'. symmetry. exact H'.
Qed.

Example trans_eq_example : forall (a b c d e f:nat),
    [a,b] = [c,d] ->
    [c,d] = [e,f] ->
    [a,b] = [e,f].
Proof.
    intros a b c d e f H1 H2. rewrite H1, H2. reflexivity.
Qed.

Theorem trans_eq : forall (a:Type) (x y z:a),
    x = y -> y = z -> x = z.
Proof.
    intros a x y z H1 H2. rewrite H1, H2. reflexivity.
Qed.

Example trans_eq_example' : forall (a b c d e f:nat),
    [a,b] = [c,d] ->
    [c,d] = [e,f] ->
    [a,b] = [e,f].
Proof. intros a b c d e f. apply trans_eq. Qed.

Definition minustwo (n:nat) : nat :=
    match n with
    | 0         => 0
    | S 0       => 0
    | S (S p)   => p
    end.

 
Example trans_eq_ex : forall (n m p q:nat),
    m = (minustwo p) ->
    (n + q) = m ->
    (n + q) = (minustwo p).
Proof.
    intros n m p q H1 H2. apply trans_eq with (y:= m).
    exact H2. exact H1.
Qed.



