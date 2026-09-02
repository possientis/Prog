Require Import bool.
Require Import nat.
Require Import dictionary.
Require Import state.
Require Import syntax.
Require Import eval.
Require Import equiv.


Definition prog_a : com :=
  WHILE BNot (BLe (AKey x) (ANum 0)) DO
    x ::= APlus (AKey x) (ANum 1)
  END.

Definition prog_b : com :=
  IFB BEq (AKey x) (ANum 0) THEN
    x ::= APlus (AKey x) (ANum 1) ;;
    y ::= ANum 1
  ELSE
    y ::= ANum 0
  FI;;
  x ::= AMinus (AKey x) (ANum 1) ;;
  y ::= ANum 0.

Definition prog_c : com :=
    SKIP.

Definition prog_d : com :=
    WHILE BNot (BEq (AKey x) (ANum 0)) DO
        x ::= APlus (AMult (AKey x) (AKey y)) (ANum 1)
    END.
 
Definition prog_e : com :=
    y ::= ANum 0.

Definition prog_g : com :=
    WHILE BTrue DO
        SKIP
    END.


Definition prog_h : com :=
    WHILE BNot (BEq (AKey x) (AKey x)) DO
        x ::= APlus (AKey x) (ANum 1)
    END.

Theorem test_equiv1 : aequiv (AMinus (AKey x) (AKey x)) (ANum 0).
Proof. intros e. simpl. apply minus_n_n. Qed.

Theorem test_equiv2 : bequiv (BEq (AMinus (AKey x) (AKey x)) (ANum 0)) BTrue.
Proof. intros e. simpl. rewrite minus_n_n. reflexivity. Qed.


Example test_congruence1 : cequiv
    (x ::= ANum 0;;
     IFB (BEq (AKey x) (ANum 0))
     THEN
        y ::= ANum 0
     ELSE
        y ::= ANum 17
     FI)

     (x ::= ANum 0;;
      IFB (BEq (AKey x) (ANum 0))
      THEN
        y ::= AMinus (AKey x) (AKey x)
      ELSE
        y ::= ANum 17
      FI).
Proof.
    apply CSeq_congruence. 
    - apply refl_cequiv.
    - apply CIf_congruence.
        + apply refl_bequiv.
        + apply CAss_congruence.
            { apply sym_aequiv. apply test_equiv1. }
        + apply refl_cequiv.
Qed.
            

