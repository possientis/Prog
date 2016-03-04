Require Import Arith.

Parameters (prime_divisor : nat -> nat)
           (prime : nat -> Prop)
           (divides : nat->nat->Prop).
