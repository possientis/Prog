Require Import nat.
Require Import syntax.
Require Import transform.

Fixpoint optimize_0plus_aexp (a:aexp) : aexp :=
    match a with 
    | ANum n            => ANum n
    | AKey k            => AKey k
    | APlus (ANum 0) a2 => optimize_0plus_aexp a2
    | APlus a1 a2       => APlus  (optimize_0plus_aexp a1)(optimize_0plus_aexp a2)
    | AMinus a1 a2      => AMinus (optimize_0plus_aexp a1)(optimize_0plus_aexp a2)
    | AMult a1 a2       => AMult  (optimize_0plus_aexp a1)(optimize_0plus_aexp a2)
    end.

(* need to change this definition *)
Fixpoint optimize_0plus_bexp (b:bexp) : bexp :=
    match b with
    | BTrue         => BTrue
    | BFalse        => BFalse
    | BEq a1 a2     => BEq (optimize_0plus_aexp a1) (optimize_0plus_aexp a2)
    | BLe a1 a2     => BLe (optimize_0plus_aexp a1) (optimize_0plus_aexp a2)
    | BNot b1       => BNot (optimize_0plus_bexp b1)
    | BAnd b1 b2    => BAnd (optimize_0plus_bexp b1) (optimize_0plus_bexp b2)
    end.

Definition optimize_0plus_com := ctrans optimize_0plus_aexp optimize_0plus_bexp.

(*
Lemma optimize_0plus_bexp_is_btrans : forall (b:bexp),
    optimize_0plus_bexp b = btrans optimize_0plus_aexp b.
Proof.
    intros b. induction b; try (reflexivity).
    -


Show.
*)


