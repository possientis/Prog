
Inductive natprod : Type :=
    | pair : nat -> nat -> natprod
    .
(*
Check pair 3 5.
*)

Definition fst (p:natprod) : nat :=
    match p with
        | pair x y  => x
    end.

Definition snd (p:natprod) : nat :=
    match p with
        | pair x y => y
    end.
(*
Compute fst (pair 3 5).
Compute snd (pair 3 5).
*)

Notation "( x , y )" := (pair x y).
(*
Compute fst (3,5).
Compute snd (3,5).
*)

Definition fst' (p:natprod) : nat :=
    match p with
        | (x,y) => x
    end.

Definition snd' (p:natprod) : nat :=
    match p with
        | (x,y) => y
    end.
(*
Compute fst' (3,5).
Compute snd' (3,5).
*)

Definition swap_pair (p:natprod) : natprod :=
    match p with
        | (x,y) => (y,x)
    end.
(*
Compute swap_pair (3,5).
*)

Theorem surjective_pairing' : forall n m:nat, 
    (n,m) = (fst (n,m), snd (n,m)).
Proof. reflexivity. Qed.

Theorem surjective_pairing : forall p:natprod,
    p = (fst p, snd p).
Proof.
    destruct p as [n m]. reflexivity.
Qed.

Theorem snd_fst_is_swap : forall p:natprod,
    (snd p, fst p) = swap_pair p.
Proof.
    destruct p as [n m]. reflexivity.
Qed.

Theorem fst_swap_is_snd : forall p:natprod,
    fst (swap_pair p) = snd p.
Proof.
    destruct p as [n m]. reflexivity.
Qed.


