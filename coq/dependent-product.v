Require Import Arith.

Parameters (prime_divisor : nat -> nat)
           (prime         : nat -> Prop)
           (divides       : nat->nat->Prop).

Check (prime (prime_divisor 220)).
Check (divides (prime_divisor 220) 220).

Check (divides 3).

Parameter binary_word     : nat -> Set.
Definition  short : Set   := binary_word 32. 
Definition  long  : Set   := binary_word 64. 

Print and.

Check (not (divides 3 81)).
Check (let d := prime_divisor 220 in prime d /\ divides d 220).

Check prod.
Check list.
Check list nat.
Check list Set.
Check list Prop.

Require Import List.

Parameters (decomp : nat -> list nat)(decomp2 : nat -> nat*nat).

Check (decomp 220).
Check (decomp2 220).
Check (Prop->Prop).
Check (Prop->Prop->Prop).
Check (Set->Set).

Parameter prime_divisor_correct :
  forall n:nat, 2 <= n -> let d := prime_divisor n in prime d /\ divides d n.
Parameter binary_word_concat :
  forall n p:nat, binary_word n -> binary_word p -> binary_word (n+p).

Check cons.
Check nil.
Check (forall A B:Set, A->B->A*B).
Check pair.


Check le_n.
Check le_S.

Check (le_S _ _ (le_S _ _ (le_n 36))).
Check (prime_divisor_correct 220).

Parameter iterate: forall A:Set, (A->A)->nat->A->A.
Check iterate.
Check (iterate nat).
Check (iterate _ (mult 2)).
Check (iterate _ (mult 2) 10).
Check (iterate _ (mult 2) 10 1).

Check (binary_word_concat 32).
Check (binary_word_concat 32 32).

Definition twice : forall A:Set, (A->A)->A->A :=
  fun A f a => f (f a).

Require Import ZArith.

Check (twice Z).
Check (twice Z (fun z => (z*z)%Z)).

Check (twice _ S 56).
Eval compute in (twice _ S 56).

Definition func1 := (twice (nat->nat) (fun f x => f (f x)) (mult 3)).
Check func1.

Eval compute in (func1 1).


