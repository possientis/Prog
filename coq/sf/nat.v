Require Import bool.

Module Playground1.

Inductive nat : Type :=
    | O : nat
    | S : nat -> nat
    .


End Playground1.

Definition pred (n:nat) : nat :=
    match n with    
        | O     => O
        | S p   => p
    end.


(* using nat from standard lib *)

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

Fixpoint evenb (n:nat) : bool :=
    match n with 
        | O         => true
        | S O       => false
        | S (S p)   => evenb p
    end.

Definition oddb (n:nat) : bool := negb (evenb n).

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

Module Playground2.

Fixpoint plus (n:nat)(m:nat) : nat :=
    match n with 
        | O     => m
        | S p   => S (plus p m)
    end.

Fixpoint mult (n m:nat) : nat :=
    match n with 
        | O     => O
        | S p   => plus m (mult p m)
    end.

(*
Compute plus 3 2.
Compute plus 1540 3000. (* stack overflow pretty soon *)
*)

Example test_mult1: mult 3 3 = 9.
Proof. simpl. reflexivity. Qed.


Fixpoint minus (n m:nat) : nat :=
    match n,m with
        | O   , _   => O
        | S _ , O   => n
        | S p , S q => minus p q
    end.

Example test_minus1: minus 10 3 = 7.
Proof. simpl. reflexivity. Qed.


End Playground2.

Fixpoint exp (base power : nat) : nat :=
    match power with
        | O     => S O
        | S p   => mult base (exp base p)
    end.

Example test_exp1: exp 3 4 = 81.
Proof. simpl. reflexivity. Qed.


Fixpoint fact (n:nat) : nat :=
    match n with
        | O     => 1
        | S p   => mult n (fact p)
    end.


Example test_fact1: fact 5 = 120.
Proof. simpl. reflexivity. Qed.


Notation "x + y" := (plus x y) (at level 50, left associativity).

(*
Compute 5 + 3 + 2 + 15.
*)

Notation "x - y" := (minus x y) (at level 50, left associativity).

(*
Compute 10 - 2 - 4.
*)

Notation "x * y" := (mult x y) (at level 40, left associativity).

(*
Compute 10 + 3 * 4.
Check plus 4 3.
*)

Fixpoint eqb (n m:nat) : bool := 
    match n with
        | O     =>  match m with
                        | O     => true
                        | S _   => false
                    end
        | S p   =>  match m with
                        | O     => false
                        | S q   => eqb p q
                    end
    end.

(*
Compute eqb 0 0.
Compute eqb 43 12.
Compute eqb 56 56.
*)

Fixpoint leb (n m:nat) : bool :=
    match n with
        | O     =>  true
        | S p   =>  match m with
                        | O     => false
                        | S q   => leb p q
                    end
    end.

(*
Compute leb 23 24.
Compute leb 24 24.
Compute leb 25 24.
*)

Definition ltb (n m:nat) : bool :=
    andb (leb n m) (negb (eqb n m)).    



(*
Compute ltb 23 24.
Compute ltb 24 24.
Compute ltb 25 24.
*)

Theorem plus_0_n : forall n:nat, 0 + n = n.
Proof.
    intros n. simpl. reflexivity.
Qed.

Theorem plus_0_n' : forall n:nat, 0 + n = n.
Proof.
    intros n. reflexivity.
Qed.

Theorem plus_1_n : forall n:nat, 1 + n = S n.
Proof.
    intros n. reflexivity.
Qed.

Theorem mult_0_n : forall n:nat, 0 * n = 0.
Proof.
    intros n. reflexivity.
Qed.

Theorem plus_n_0 : forall n:nat, n + 0 = n.
Proof.
    intros n. elim n.
    clear n. reflexivity.
    clear n. intros n H. simpl. rewrite H. reflexivity.
Qed.

Theorem mult_1_n : forall n:nat, 1 * n = n.
Proof.
    intros n. simpl. apply plus_n_0.
Qed.

Theorem plus_id_example: forall n m:nat, 
    n = m -> n + n = m + m.
Proof.
    intros n m H. rewrite H. reflexivity.
Qed.

Theorem plus_id_exercise: forall n m o: nat,
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

Theorem mult_0_plus : forall n m:nat,
    (0 + n) * m = n * m.
Proof.
    intros n m. rewrite plus_0_n. reflexivity.
Qed.

Theorem mult_S_1 : forall n m:nat,
    m = S n -> m * (1 + n) = m * m.
Proof.
    intros n m H. simpl. rewrite <- H. reflexivity.
Qed.

Theorem plus_1_neq_0 : forall n:nat,
    eqb (n + 1) 0 = false.
Proof.
    intros n. elim n.
    clear n. simpl. reflexivity.
    clear n. intros n H. simpl. reflexivity.
Qed.

Theorem plus_1_neq_0' : forall n:nat,
    eqb (n + 1) 0 = false.
Proof.
    (* 'as' clause to name variables of constructors    *)
    (*  of inductive type. 0 is a nullary constructor   *)
    intros n. destruct n as [|n].   (* we don't need induction here *)
    - reflexivity.          (* you can skip 'simpl' *) (* using bullet for clarity *)
    - reflexivity.          (* you can skip 'simpl' *) (* using bullet for clarity *)
Qed.

Theorem plus_1_neq_0'' : forall n:nat,
    eqb (n + 1) 0 = false.
Proof.
    intros [|n].           (* shortcut for intros n. destruct n as [|n]. *) 
    - reflexivity.
    - reflexivity.
Qed.


Theorem zero_nbeq_plus_1 : forall n:nat,
    eqb 0 (n + 1) = false.
Proof.
    intros [|n].
    - reflexivity.
    - reflexivity.
Qed.

Theorem eqb_refl : forall n:nat, eqb n n = true.
Proof.
    induction n as [|n H].
    - reflexivity.
    - simpl. exact H.
Qed.



Lemma true_not_false : true <> false.
Proof.
    intro H. discriminate H.
Qed.

Theorem eqb_semantics : forall n m:nat,
    n = m <-> eqb n m = true.
Proof.
 intros n m. split.
 - intros H. rewrite H. apply eqb_refl.
 - generalize m. clear m. induction n as [|n H]. 
    + destruct m.
        { intros H. reflexivity. }
        { simpl. intros H. discriminate H. }
    + destruct m.
        { simpl. intros H'. discriminate H'. }
        { simpl. intros H'. 
          assert (n = m) as H''. { apply H. exact H'. }
          rewrite H''. reflexivity. }
Qed.


Theorem eqb_semantics' : forall (n m: nat),
    n = m <-> eqb n m = true.
Proof.
    split.
    - intros H. rewrite H. apply eqb_refl. 
    - generalize m. clear m. induction n as [| n H].
        + destruct m. 
            { intros. reflexivity. }
            { simpl. intros H. inversion H. }
        + destruct m.
            { simpl. intros H'. inversion H'. }
            { simpl. intros H'. apply H in H'. rewrite H'. reflexivity. }
Qed.
        

Theorem eqb_sym : forall (n m:nat),
    eqb n m = eqb m n.
Proof.
    induction n as [|n H].
    - destruct m. 
        + reflexivity.
        + reflexivity.
    - destruct m.
        + reflexivity. 
        + apply H.
Qed.

Theorem eqb_trans : forall (n m p:nat),
    eqb n m = true -> eqb m p = true -> eqb n p = true.
Proof.
   intros n m p Hnm Hmp. 
   apply eqb_semantics. 
   apply eqb_semantics in Hnm.
   apply eqb_semantics in Hmp.
   apply eq_trans with (y:=m).
   exact Hnm.
   exact Hmp.
Qed.

Theorem eqb_false_iff : forall (n m:nat),
    eqb n m = false <-> n <> m.
Proof.
    intros n m. split.
    - intros H H'. rewrite H' in H. rewrite eqb_refl in H. inversion H.
    - intros H. destruct (eqb n m) eqn: Enm. 
        + apply eqb_semantics in Enm. exfalso. apply H. exact Enm.
        + reflexivity.
Qed.



