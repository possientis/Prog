Require Import ZArith.
Require Import key. (* need to compile key.v *)

Open Scope Z_scope.

Module ZKey : KEY.
  Definition A:=Z.

(*
Check Z_eq_dec.
Z.eq_dec
     : forall x y : Z, {x = y} + {x <> y}
*)

  Definition eqdec := Z_eq_dec.

End ZKey.

(*
Check ZKey.A.
ZKey.A
     : Set
*)

(*
Check ZKey.eqdec.
  ZKey.eqdec
       : forall a b : ZKey.A, {a = b} + {a <> b}
*)

(*  implementation details are hidden
Print ZKey.A.
*** [ ZKey.A : Set ]
*)

(*
  you only see spec from signature KEY
Print ZKey.eqdec.
Print ZKey.eqdec.
*** [ ZKey.eqdec : forall a b : ZKey.A, {a = b} + {a <> b} ]
*)

(* The fact that A:=Z is hidden becomes a problem
Check (ZKey.eqdec (9*7)(8*8)).
Error: The term "9 * 7" has type "Z" while it is expected to have type
 "ZKey.A".
*)


Module ZKey' <: KEY. (* not hiding implementation *)
  Definition A:=Z.
  Definition eqdec := Z_eq_dec.
End ZKey'.

(* This now works *)
Check (ZKey'.eqdec (9*7)(8*8)).
(*
ZKey'.eqdec (9 * 7) (8 * 8)
     : {9 * 7 = 8 * 8} + {9 * 7 <> 8 * 8}
*)

(* implementation details now visible, which can create problem for 
future evolution of the module ZKey' *)
Print ZKey'.eqdec.
(*
ZKey'.eqdec = Z.eq_dec
     : forall x y : Z, {x = y} + {x <> y}
*)

Module ZKey'' : KEY with Definition A:=Z.
  Definition A:=Z. (* yes, same definition twice, odd :( *)
  Definition eqdec := Z_eq_dec.
End ZKey''.


(* This works too*)
Check (ZKey''.eqdec (9*7)(8*8)).
(*
ZKey''.eqdec (9 * 7) (8 * 8)
     : {9 * 7 = 8 * 8} + {9 * 7 <> 8 * 8}
*)

(* best of both worlds, A:=Z is visible but implementation details of
eqdec are not *)
Print ZKey''.eqdec.
(*
*** [ ZKey''.eqdec : forall a b : ZKey''.A, {a = b} + {a <> b} ]
*)



