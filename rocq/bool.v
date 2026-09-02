Inductive bool : Set := true | false.

Lemma duality : forall b:bool, b = true \/ b = false.
  intro b.
  elim b.
  left.
  reflexivity.
  right.
  reflexivity.
  Restart.
  induction b;auto.
Qed.

Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.

Definition prim_rec := nat_rec(fun i:nat => nat).

(* primitive recursion *)
Check prim_rec.
Eval cbv beta in 
  (fun _ : nat => nat) O -> (forall n : nat, (fun _ : nat => nat) n 
                         -> (fun _ : nat => nat) (S n)) 
                         -> forall n : nat, (fun _ : nat => nat) n.

Definition addition (n m : nat) :=
  prim_rec m (fun p rec:nat => S rec) n.

Eval compute in (addition (S (S O)) (S (S (S O)))).


Fixpoint plus (n m:nat) {struct n} : nat :=
  match n with
  | O   => m
  | S p => S (plus p m)
  end.
