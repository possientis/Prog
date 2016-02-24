Require Import Arith.
Require Import ZArith.
Require Import Bool.

Open Scope Z_scope.

Locate "_ * _".

Print Scope Z_scope.

Check 33. (* default scope is Z *)
Check 33%nat. (* 33 interpreted within scope nat_scope with key 'nat' *)
Check 0. (* : Z *)
Check O. (* : nat *)

Open Scope nat_scope.
Check 33. (* : nat *)
Check 0. (* nat *)
Check 33%Z.
Check (-12)%Z.
Check (33%nat).

Check true. (* : bool *)
Check false. (* : bool *)


Check plus.
Check Zplus.
Check negb.
Check ifb. 
Check S.
Check 0.
Check O.
Check S (S (S 0)).
Check mult (mult 5 (minus 5 4)) 7.
Check (5*(5-4)*7).

Unset Printing Notations.
Check 4.
Check (5*(5-4)*7).
Set Printing Notations.
Open Scope Z_scope.
Check (Zopp (Zmult 3 (Zmult (-5) (-8)))).
Check ((-4)*(7-7)).
Open Scope nat_scope.
Check Zabs_nat.
Check (5 + Zabs_nat (5-19)).

Check (fun n (z:Z) f => (n + (Zabs_nat(f z)))%nat).
Check (fun n _ : nat => n).
Check (fun n p:nat => n).

Definition f := 
  fun n p: nat => (let diff := n-p in
                   let square := diff*diff in
                   square*(square+n)%nat).
Check f.
Parameter max_int : Z.

Open Scope Z_scope.
Definition min_int := 1 - max_int.
Print min_int.

Definition cube1 := fun z:Z => z*z*z.
Definition cube2 (z:Z) : Z := z*z*z.
Definition cube3 z := z*z*z.
Print cube1.
Print cube2.
Print cube3.

Definition Z_thrice (f:Z->Z)(z:Z) := f (f (f z)).
Print Z_thrice.
Definition plus9 := Z_thrice (Z_thrice (fun z:Z => z + 1)).
Eval compute in plus9 2.


