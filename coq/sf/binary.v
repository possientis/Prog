Inductive bin : Type :=
    | B : bin
    | Q : bin -> bin (* twice the binary number *)
    | I : bin -> bin (* twice the binaty number + 1 *) 
    .

Fixpoint incr (n:bin) : bin :=
    match n with
        | B     => I B
        | Q p   => I p
        | I p   => Q (incr p)
    end.


Fixpoint bin_to_nat (n:bin) : nat := 
    match n with
        | B     =>      0
        | Q p   =>      2 * bin_to_nat p
        | I p   => S (  2 * bin_to_nat p )
    end.

(*
Compute bin_to_nat B.                   (* 0 *)
Compute bin_to_nat (I B).               (* 1 *)
Compute bin_to_nat (Q (I B)).           (* 2 *)
Compute bin_to_nat (I (I B)).           (* 3 *)
Compute bin_to_nat (Q (Q (I B))).       (* 4 *)
Compute bin_to_nat (I (Q (I B))).       (* 5 *)
Compute bin_to_nat (Q (I (I B))).       (* 6 *)
Compute bin_to_nat (I (I (I B))).       (* 7 *)
Compute bin_to_nat (Q (Q (Q (I B)))).   (* 8 *)
*)

Theorem test_bin_incr1 : forall n:bin,
    bin_to_nat (incr n) = S (bin_to_nat n).
Proof.
    intros n. elim n.
    - clear n. reflexivity.
    - clear n. intros. reflexivity.
    - clear n. intros. simpl. rewrite H. rewrite <- plus_n_O.
      rewrite <- plus_n_O. simpl. rewrite <- plus_n_Sm.
      reflexivity.
Qed.

Fixpoint nat_to_bin (n:nat) : bin :=
    match n with
        | 0     => B
        | S p   => incr (nat_to_bin p)
    end.

(*
Compute nat_to_bin 0.                   (* B *)
Compute nat_to_bin 1.                   (* I B *)
Compute nat_to_bin 2.                   (* Q (I B) *)
Compute nat_to_bin 3.                   (* I (I B) *)
*)


Theorem test_bin_incr2 : forall n:nat,
    nat_to_bin (S n) = incr (nat_to_bin n).
Proof.
    intros [|n].
    - reflexivity.
    - reflexivity.
Qed.

(* beware about going the other way *)
Theorem test_nat_to_nat : forall n:nat,
    bin_to_nat (nat_to_bin n) = n.
Proof.
    intros. elim n.
    - clear n. reflexivity.
    - clear n. intros. simpl. rewrite test_bin_incr1. rewrite H. reflexivity.
Qed.




