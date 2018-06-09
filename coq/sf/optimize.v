Require Import nat.
Require Import syntax.
Require Import transform.
Require Import fold_constants.

Fixpoint optimize_0plus_aexp (a:aexp) : aexp :=
    match a with 
    | ANum n            => ANum n
    | AKey k            => AKey k
    | APlus (ANum 0) a2 => optimize_0plus_aexp a2
    | APlus a1 a2       => APlus  (optimize_0plus_aexp a1)(optimize_0plus_aexp a2)
    | AMinus a1 a2      => AMinus (optimize_0plus_aexp a1)(optimize_0plus_aexp a2)
    | AMult a1 a2       => AMult  (optimize_0plus_aexp a1)(optimize_0plus_aexp a2)
    end.

Definition optimize_0plus_bexp:= btrans optimize_0plus_aexp.
Definition optimize_0plus_com := ctrans optimize_0plus_aexp optimize_0plus_bexp.

(* need to prove soundness *)
Definition optimize_aexp (a:aexp) : aexp := 
    optimize_0plus_aexp(fold_constants_aexp a).
Definition optimize_bexp := btrans optimize_aexp.
Definition optimize_com  := ctrans optimize_aexp optimize_bexp.

(* do we care ?
Lemma same_optimize_bexp : forall (b:bexp), 
    optimize_bexp b = optimize_0plus_bexp (fold_constants_bexp b).
Proof.
    intros b. induction b; try (reflexivity).
    - simpl. unfold optimize_bexp, 
                    optimize_0plus_bexp, 
                    fold_constants_bexp,
                    optimize_aexp. 
      simpl. rename a into a1. rename a0 into a2.

Show.
*)

