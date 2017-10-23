Require Import list.
Require Import nat.
Require Import bool.

Inductive option (a:Type) : Type :=
    | Some : a -> option a
    | None : option a
    .

Arguments Some {a} _.
Arguments None {a}.

Fixpoint nth (a:Type) (l:list a) (n:nat) : option a :=
    match l with
    | []        => None
    | x::xs     => 
        match eqb n 0 with
        | true      => Some x
        | false     => nth a xs (pred n)
        end
    end.

Arguments nth {a} _ _.
     

Example test_nth1 : nth ([]:list nat) 0 = None.
Proof. reflexivity. Qed.

Example test_nth2 : nth ([]:list nat) 1 = None.
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

Definition hd_error (a:Type)(l:list a) : option a :=
    match l with
    | []        => None
    | x::xs     => Some x
    end.

Arguments hd_error {a} _.

Example test_hd_error1 : hd_error ([]:list nat) = None.
Proof. reflexivity. Qed.


Example test_hd_error2 : hd_error [1] = Some 1.
Proof. reflexivity. Qed.


Example test_hd_error3 : hd_error [5,4,3] = Some 5.
Proof. reflexivity. Qed.


