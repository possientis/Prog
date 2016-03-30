Set Implicit Arguments.


Print nat. (* Inductive nat : Set :=  O : nat | S : nat -> nat *)
Check nat_ind.
(*
forall P : nat -> Prop,
       P 0 -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n
*)

Print nat_ind.
(*
nat_ind = 
fun P : nat -> Prop => nat_rect P
     : forall P : nat -> Prop,
              P 0 -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n
*)

Print nat_rec.
(*
nat_rec = 
fun P : nat -> Set => nat_rect P
     : forall P : nat -> Set,
              P 0 -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n
*)


Print nat_rect.
(*
fun (P : nat -> Type) (f : P 0) (f0 : forall n : nat, P n -> P (S n)) =>
fix F (n : nat) : P n :=
  match n as n0 return (P n0) with
    | 0 => f
    | S n0 => f0 n0 (F n0)
  end
  : forall P : nat -> Type,
    P 0 -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n
*)

Check plus_O_n. (* forall n : nat, 0 + n = n *)
Check plus_Sn_m. (* forall n m : nat, S n + m = S (n + m) *)

Theorem plus_assoc: forall x y z:nat,
  (x+y)+z = x+(y+z).
Proof.
  intros x y z. elim x. rewrite plus_O_n. rewrite plus_O_n. reflexivity.
  intros x' IH. rewrite plus_Sn_m. rewrite plus_Sn_m. rewrite plus_Sn_m.
  rewrite IH. reflexivity.
Qed.

(* defining (_ * 2) by recursion *)
Fixpoint mult2 (n:nat) : nat :=
  match n with
  | 0   => 0
  | S p => S (S (mult2 p))
  end.

Print plus.

Fixpoint mult3 (n:nat) :nat :=
  match n with
  | 0   => 0
  | S p => S (S (S mult3 p))
  end.


(*

plus = 
fix plus (n m : nat) {struct n} : nat :=
  match n with
    | 0 => m
    | S p => S (plus p m)
  end
: nat -> nat -> nat

*)

