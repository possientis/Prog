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


Fixpoint optimize_0plus_bexp (b:bexp) : bexp :=
    match b with
    | BTrue         => BTrue
    | BFalse        => BFalse
    | BEq a1 a2     => BEq (optimize_0plus_aexp a1) (optimize_0plus_aexp a2)
    | BLe a1 a2     => BLe (optimize_0plus_aexp a1) (optimize_0plus_aexp a2)
    | BNot b1       => BNot (optimize_0plus_bexp b1)
    | BAnd b1 b2    => BAnd (optimize_0plus_bexp b1) (optimize_0plus_bexp b2)
    end.


Fixpoint optimize_0plus_com (c:com) : com :=
    match c with
    | SKIP          => SKIP
    | k ::= a       => k ::= (optimize_0plus_aexp a)
    | c1 ;; c2      => (optimize_0plus_com c1) ;; (optimize_0plus_com c2)
    | CIf b c1 c2   => match (optimize_0plus_bexp b) with
                       | BTrue      => optimize_0plus_com c1
                       | BFalse     => optimize_0plus_com c2
                       | b'         => CIf b' (optimize_0plus_com c1)
                                              (optimize_0plus_com c2)
                       end
    | CWhile b c1   => match (optimize_0plus_bexp b) with
                       | BTrue      => CWhile BTrue SKIP (* oo-loop all the same *)
                       | BFalse     => SKIP
                       | b'         => CWhile b' (optimize_0plus_com c1)
                       end
    end.

Lemma optimize_0plus_is_ctrans : forall (c:com),
    optimize_0plus_com c = ctrans optimize_0plus_aexp optimize_0plus_bexp c.
Proof.
    intros c. induction c; 
    try (reflexivity);
    try (simpl; rewrite <- IHc; reflexivity);
    try (simpl; rewrite <- IHc1, IHc2; reflexivity).
Qed.


