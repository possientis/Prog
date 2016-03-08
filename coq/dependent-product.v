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

Definition compose : forall A B C: Set, (A->B)->(B->C)->A->C :=
  fun A B C f g x => g (f x).

Print compose.

Check (compose _ _ _ Zabs_nat (plus 78) 45%Z).


Implicit Arguments compose [A B C].

(*
Set Implicit Arguments.
*)

Check (compose Zabs_nat (plus 78)).

Check compose.
Print compose.

Implicit Arguments le_S [n m].

Check le_S.
Check (le_S (n := 45)).
Print compose.

Reset compose.
Set Implicit Arguments.
(* Arguments which can be inferred will automatically be implicit *)

Definition compose (A B C: Set)(f: A->B)(g: B->C)(a: A) := g(f a).
Print compose. (* A B C are implicit, without command 'Implicit Arguments compose [A B C]' *)

Definition thrice (A: Set)(f : A->A) := compose f (compose f f).
Print thrice.

Unset Implicit Arguments.
Print thrice.

Eval cbv beta delta in thrice (thrice (thrice S)) 0.

Definition short_concat : short -> short -> long :=
  binary_word_concat 32 32.

Check short_concat.

Require Import Reals.

Check eq.
Check R.
Check eq (A:=R).

Check eq R.
Print eq.


Section A_declared.
  Variables (A:Set)(P Q:A->Prop)(R:A->A->Prop).
  Theorem all_perm : (forall a b:A, R a b) -> forall a b:A, R b a.
  Proof.
    intro H.
    intro a.
    intro b.
    apply H.
  Qed.
  Theorem all_imp_dist : 
    (forall a:A, P a -> Q a) -> (forall a:A, P a)-> forall a:A, Q a.
  Proof.
    intros Hpq Hp a.
    apply Hpq.
    apply Hp.
  Qed.

  Theorem all_delta : (forall a b: A, R a b) -> forall a:A, R a a.
  Proof.
    intros H a.
    apply H.
  Qed.
End A_declared.

Check (forall n:nat, 0 < n -> nat).

Check pair.

Check iterate.
Print iterate.

Definition my_plus: nat->nat->nat := iterate nat S.
Definition my_mult (n p:nat) : nat :=
  iterate nat (my_plus n) p 0.
Definition my_expo (x n:nat) : nat :=
  iterate nat (my_mult x) n 1.






