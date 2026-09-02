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

Example test_nth3 : nth [12] 0 = Some 12.
Proof. reflexivity. Qed.

Example test_nth4 : nth [12] 1 = None.
Proof. reflexivity. Qed.

Example test_nth5 : nth [12,8] 0 = Some 12.
Proof. reflexivity. Qed.

Example test_nth6 : nth [12,3] 1 = Some 3.
Proof. reflexivity. Qed.

Example test_nth7 : nth [12,3] 2 = None.
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

Example test_optione_elim1 : option_elim 12 None = 12.
Proof. reflexivity. Qed.


Example test_optione_elim2 : option_elim 3 (Some 5) = 5.
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






