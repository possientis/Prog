(* delta-reduction *)
Require Import ZArith.
Open Scope Z_scope.

Definition Zsqr (z:Z) : Z := z*z.
Definition myFunc (f:Z->Z)(z:Z) : Z := f(f z).

(* cbv call by value strategy *)
Eval cbv delta [myFunc Zsqr] in (myFunc Zsqr).  (* looks like unfold *)

Eval cbv delta [myFunc] in (myFunc Zsqr).

Eval cbv beta delta [myFunc Zsqr] in (myFunc Zsqr).

Eval compute in (myFunc Zsqr 3).

