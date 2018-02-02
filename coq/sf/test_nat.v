Require Import bool.
Require Import nat.

Definition minustwo (n:nat) : nat :=
    match n with
        | O         => O
        | S O       => O
        | S (S p)   => p
    end.

(*
Check S (S (S (S O))).
Compute minustwo 4.
Check S.
Check Playground1.pred.
Check minustwo.
*)

Example test_evenb0: evenb 0 = true.
Proof. simpl. reflexivity. Qed.

Example test_evenb1: evenb 1 = false.
Proof. simpl. reflexivity. Qed.

Example test_evenb2: evenb 2 = true.
Proof. simpl. reflexivity. Qed.


Example test_oddb0: oddb 0 = false.
Proof. simpl. reflexivity. Qed.

Example test_oddb1: oddb 1 = true.
Proof. simpl. reflexivity. Qed.

Example test_oddb2: oddb 2 = false.
Proof. simpl. reflexivity. Qed.

(*
Compute plus 3 2.
Compute plus 1540 3000. (* stack overflow pretty soon *)
*)

Example test_mult1: mult 3 3 = 9.
Proof. simpl. reflexivity. Qed.


Example test_minus1: minus 10 3 = 7.
Proof. simpl. reflexivity. Qed.


Example test_exp1: exp 3 4 = 81.
Proof. simpl. reflexivity. Qed.

Example test_fact1: fact 5 = 120.
Proof. simpl. reflexivity. Qed.

(*
Compute 5 + 3 + 2 + 15.
*)

(* 
Compute 10 - 2 - 4.
*)

(*
Compute 10 + 3 * 4.
Check plus 4 3.
*)

(*
Compute eqb 0 0.
Compute eqb 43 12.
Compute eqb 56 56.
*)

(*
Compute leb 23 24.
Compute leb 24 24.
Compute leb 25 24.
*)

(*
Compute ltb 23 24.
Compute ltb 24 24.
Compute ltb 25 24.
*)

Lemma plus_0_n' : forall n:nat, 0 + n = n.
Proof.
    intros n. reflexivity.
Qed.


Lemma plus_id_example: forall n m:nat, 
    n = m -> n + n = m + m.
Proof.
    intros n m H. rewrite H. reflexivity.
Qed.

Lemma plus_id_exercise: forall n m o: nat,
   n = m -> m = o -> n + m = m + o.
Proof.
    intros n m o H1 H2. rewrite H1. rewrite <- H2. reflexivity.
Qed.

(*
Theorem plus_comm : forall n m:nat, 
    n + m = m + n.
Proof.
Admitted.  (* useful when writing bigger proofs *)
*)

Lemma plus_1_neq_0' : forall n:nat,
    eqb (n + 1) 0 = false.
Proof.
    (* 'as' clause to name variables of constructors    *)
    (*  of inductive type. 0 is a nullary constructor   *)
    intros n. destruct n as [|n].   (* we don't need induction here *)
    - reflexivity.          (* you can skip 'simpl' *) (* using bullet for clarity *)
    - reflexivity.          (* you can skip 'simpl' *) (* using bullet for clarity *)
Qed.

Lemma plus_1_neq_0'' : forall n:nat,
    eqb (n + 1) 0 = false.
Proof.
    intros [|n].           (* shortcut for intros n. destruct n as [|n]. *) 
    - reflexivity.
    - reflexivity.
Qed.



