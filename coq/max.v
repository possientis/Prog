Set Implicit Arguments.
Require Import Arith.Max.

Check max_lub.    (* forall n m p : nat, n <= p -> m <= p -> max n m <= p *)
Check max_lub_r.  (* forall n m p : nat, max n m <= p -> m <= p *)
Check max_lub_l.  (* forall n m p : nat, max n m <= p -> n <= p *)
Check le_max_r.   (* forall n m : nat, m <= max n m *)
Check le_max_l.   (* forall n m : nat, n <= max n m *)
Check max_r.      (* forall n m : nat, n <= m -> max n m = m *)
Check max_l.      (* forall n m : nat, m <= n -> max n m = n *)
Check max_case.   (* forall (n m : nat) (P : nat -> Type), 
                     P n -> P m -> P (max n m) *)
Check max_0_l.

