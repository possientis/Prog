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
  | S p => S (S (S (mult3 p)))
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

Definition less_than_three (n:nat) : bool :=
  match n with 
  | 0         => true
  | S 0       => true
  | S (S 0)   => true 
  | other     => false
  end.

Eval compute in (less_than_three 0).
Eval compute in (less_than_three 1).
Eval compute in (less_than_three 2).
Eval compute in (less_than_three 3).
Eval compute in (less_than_three 4).

Fixpoint plus2 (n m : nat) : nat :=
  match m with 
    | 0   => n
    | S p => S (plus2 n p)
  end.
Check plus_n_O.
Check plus_n_Sm. (* forall n m : nat, S (n + m) = n + S m *)

Theorem same_plus: forall n m : nat, plus2 n m = n + m.
Proof.
  intros n m. elim m. simpl. apply plus_n_O. clear m. intros m H. simpl.
  rewrite <- plus_n_Sm. rewrite H. reflexivity.
Qed.

Fixpoint sum_f_acc (n:nat)(f: nat->nat)(acc: nat) :nat :=
  match n with
    | 0     => acc
    | S p   => sum_f_acc p f (acc + (f p))
  end.

Definition sum_f (n:nat)(f:nat->nat) : nat := sum_f_acc n f 0.

Eval compute in (sum_f 5 (fun n => (S n)*(S n))).


Fixpoint iterate (A:Set)(f:A->A)(n:nat)(x:A){struct n} : A :=
  match n with
    | 0   => x
    | S p => f (iterate f p x)
  end.

Fixpoint two_power (n:nat) : nat :=
  match n with
    | 0   => 1
    | S p => 2 * two_power p
  end.

Eval compute in two_power 10.






