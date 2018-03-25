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




