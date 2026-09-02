Inductive nat : Type :=
    | O : nat
    | S : nat -> nat
    .

Notation "0" := (O).
Notation "1" := (S 0).

Fixpoint plus (n:nat)(m:nat) : nat :=
    match n with 
        | 0    => m
        | S p  => S (plus p m)
    end.
        

Notation "x + y" := (plus x y) (at level 50, left associativity).

Lemma plus_0_n : forall (n:nat), 0 + n = n. 
Proof.
intros n. simpl. reflexivity.
Qed.

Lemma plus_n_0 : forall (n:nat), n + 0 = n.
Proof.
intros n. induction n as [|n IH].  
    - simpl. reflexivity.
    - simpl. rewrite IH. reflexivity.
Qed.

Lemma plus_1_n : forall (n:nat), 1 + n = S n.
Proof.
intros n. simpl. reflexivity.
Qed.


Lemma plus_n_1 : forall (n:nat), n + 1 = S n.
Proof.
intros n. induction n as [|n IH].
    - simpl. reflexivity.
    - simpl. rewrite IH. reflexivity.
Qed.


Lemma plus_n_Sm : forall (n:nat)(m:nat), n + S m = S (n + m).
Proof.
intros n. induction n as [|n IH].
    - intros m. reflexivity.
    - intros m. simpl. rewrite IH. reflexivity.
Qed.
    







    




    
    



     
