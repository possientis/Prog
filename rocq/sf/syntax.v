Require Import bool.
Require Import nat.
Require Import dictionary.

Inductive aexp : Type :=
| ANum   : nat -> aexp
| AKey   : Key -> aexp
| APlus  : aexp -> aexp -> aexp
| AMinus : aexp -> aexp -> aexp
| AMult  : aexp -> aexp -> aexp
.


Inductive bexp : Type :=
| BTrue  : bexp
| BFalse : bexp
| BEq    : aexp -> aexp -> bexp
| BLe    : aexp -> aexp -> bexp
| BNot   : bexp -> bexp
| BAnd   : bexp -> bexp -> bexp
.


Inductive com : Type :=
| CSkip  : com
| CAss   : Key -> aexp -> com
| CSeq   : com -> com -> com
| CIf    : bexp -> com -> com -> com
| CWhile : bexp -> com -> com
.

Notation "'SKIP'"    := CSkip.

Notation "x '::=' a" := (CAss x a) 
(at level 60).

Notation "c1 ;; c2"  := (CSeq c1 c2) 
(at level 80, right associativity). 

Notation "'WHILE' b 'DO' c 'END'" := (CWhile b c) 
(at level 80, right associativity).

Notation "'IFB' b 'THEN' c1 'ELSE' c2 'FI'" := (CIf b c1 c2) 
(at level 80, right associativity).

Fixpoint no_whiles (c:com) : bool :=
    match c with
    | SKIP                      => true
    | _ ::= _                   => true
    | c1 ;; c2                  => andb (no_whiles c1) (no_whiles c2)
    | IFB _ THEN c1 ELSE c2 FI  => andb (no_whiles c1) (no_whiles c2)
    | WHILE _ DO _ END          => false
    end.

Inductive no_whilesR : com -> Prop :=
| NW_Skip : no_whilesR SKIP
| NW_Ass  : forall k a, no_whilesR (k ::= a)
| NW_Seq  : forall c1 c2, no_whilesR c1 -> no_whilesR c2 -> no_whilesR(c1 ;; c2)
| NW_If   : forall b c1 c2, no_whilesR c1 -> no_whilesR c2 -> 
                no_whilesR (IFB b THEN c1 ELSE c2 FI)
.

Theorem no_whiles_iff : forall (c:com),
    no_whiles c = true <-> no_whilesR c.
Proof.
    intros c. split.
    - induction c as [|k a|c1 IH1 c2 IH2|b c1 IH1 c2 IH2|b c1 IH1].
        + intros _. constructor.
        + intros _. constructor.
        + simpl. rewrite andb_true_iff. intros [H1 H2]. constructor.
            { apply IH1. assumption. }
            { apply IH2. assumption. }
        + simpl. rewrite andb_true_iff. intros [H1 H2]. constructor.
            { apply IH1. assumption. }
            { apply IH2. assumption. }
        + simpl. intros H. inversion H.
    - intros H. induction H as [|k a|c1 c2 H1 IH1 H2 IH2|b c1 c2 H1 IH1 H2 IH2]. 
        + reflexivity.
        + reflexivity.
        + simpl. rewrite IH1, IH2. reflexivity.
        + simpl. rewrite IH1, IH2. reflexivity.
Qed.

