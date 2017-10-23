Require Import nat.
Require Import bool.
Require Import natlist.


Inductive natoption : Type :=
    | Some : nat -> natoption
    | None : natoption
    .

Fixpoint nth (l:natlist) (n:nat) : natoption :=
    match l with
        | nil       => None
        | x::xs     => match eqb n 0 with
                            | true      => Some x
                            | false     => nth xs (pred n)
                       end
    end. 

(* if ... then ... else syntactic sugar *)
Fixpoint nth' (l:natlist) (n:nat) : natoption :=
    match l with
        | nil       => None
        | x::xs     => if eqb n 0 then Some x else nth' xs (pred n)
    end.

Example test_nth1 : nth [] 0 = None.
Proof. reflexivity. Qed.

Example test_nth2 : nth [] 1 = None.
Proof. reflexivity. Qed.

Example test_nth3 : nth [23] 0 = Some 23.
Proof. reflexivity. Qed.

Example test_nth4 : nth [23] 1 = None.
Proof. reflexivity. Qed.

Example test_nth5 : nth [23,65] 0 = Some 23.
Proof. reflexivity. Qed.

Example test_nth6 : nth [23,65] 1 = Some 65.
Proof. reflexivity. Qed.

Example test_nth7 : nth [23,65] 2 = None.
Proof. reflexivity. Qed.

Theorem nth_nth' : forall (l:natlist) (n:nat),
    nth l n = nth' l n.
Proof.
    induction l as [| x xs H].
    - reflexivity.
    - destruct n as [| n]. 
        + reflexivity.
        + simpl. apply H.
Qed.

Definition option_elim (default:nat) (o:natoption) : nat :=
    match o with
        | None      => default
        | Some x    => x
    end.

Example test_optione_elim1 : option_elim 42 None = 42.
Proof. reflexivity. Qed.


Example test_optione_elim2 : option_elim 42 (Some 23) = 23.
Proof. reflexivity. Qed.

Definition hd_error (l:natlist) : natoption :=
    match l with
        | nil       => None
        | x::xs     => Some x
    end.

Example test_hd_error1 : hd_error [] = None.
Proof. reflexivity. Qed.


Example test_hd_error2 : hd_error [1] = Some 1.
Proof. reflexivity. Qed.


Example test_hd_error3 : hd_error [5,4,3] = Some 5.
Proof. reflexivity. Qed.

Theorem option_elim_d : forall (l:natlist) (default:nat),
    hd default l = option_elim default (hd_error l).
Proof.
    destruct l as [| x xs].
    - reflexivity.
    - reflexivity.
Qed.






