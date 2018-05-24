Require Import bool.
Require Import nat.
Require Import syntax.
Require Import eval.
Require Import state.
Require Import dictionary.
Require Import equiv.

Definition atrans_sound (atrans:aexp -> aexp) : Prop :=
    forall (a:aexp), aequiv a (atrans a).

Definition btrans_sound (btrans:bexp -> bexp) : Prop :=
    forall (b:bexp), bequiv b (btrans b).

Definition ctrans_sound (ctrans:com -> com) : Prop :=
    forall (c:com), cequiv c (ctrans c).


Fixpoint ctrans (fa:aexp -> aexp)(fb:bexp -> bexp)(c:com) : com :=
    match c with
    | SKIP          => SKIP
    | k ::= a       => k ::= (fa a)
    | c1 ;; c2      => (ctrans fa fb c1) ;; (ctrans fa fb c2)
    | CIf b c1 c2   => match (fb b) with
                       | BTrue      => ctrans fa fb c1
                       | BFalse     => ctrans fa fb c2
                       | b'         => CIf b' (ctrans fa fb c1)
                                              (ctrans fa fb c2)
                       end
    | CWhile b c1   => match (fb b) with
                       | BTrue      => CWhile BTrue SKIP (* oo-loop all the same *)
                       | BFalse     => SKIP
                       | b'         => CWhile b' (ctrans fa fb c1)
                       end
    end.







