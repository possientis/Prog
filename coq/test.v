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
