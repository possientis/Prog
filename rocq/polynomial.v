
Require Import ZArith.
Open Scope Z_scope.

Section binomial_def.
  Variables a b:Z.
  Definition binomial z:Z := a*z + b.
  Section trinomial_def.
    Variable c:Z.
    Definition trinomial z:Z := (binomial z)*z +c.
  End trinomial_def.
End binomial_def.


Definition p1: Z->Z := binomial 5 (-3).
Definition p2: Z->Z := trinomial 1 0 (-1).
Definition p3: Z->Z := trinomial 1 (-2) 1.

Section mab.
  Variables m a b: Z.
  Definition f := m*a*m.
  Definition g := m*(a+b).
End mab.

Section h_def.
  Variables a b:Z.
  Let s:Z := a+b.
  Let d:Z := a-b.
  Definition h:Z := s*s + d*d.
  Print h.
End h_def.
Print h.

(* conversion *) 


(* without zeta conversion which reduces the let... *)
Eval cbv beta delta [h] in (h 56 78).
(* with zeta comversion *)
Eval cbv beta zeta delta [h] in (h 56 78).

(* iota reduction has to do with induction scheme 
and will be explained later *)
(*
Why does this line fail, order between iota and delta seems to matter.
Eval cbv beta zeta delta iota [h] in (h 56 78).
*)

Eval cbv beta zeta iota delta [h] in (h 56 78). (* iota conversion does not work *)
Eval compute in (h 56 78).

Eval cbv in (h 56 78). (* looks like compute *)
Eval cbv [h] in (h 56 78). (* only reduces h, not 56 and 78 *)
Eval cbv delta [h] in (h 56 78). (* unfolds h *)
Eval cbv delta in (h 56 78).     (* unfolds everything *)
Eval cbv delta [h] in (h 56 78).
(*Eval cbv delta zeta [h] in (h 56 78).*) (* this fails , order matters*)
Eval cbv zeta delta [h] in (h 56 78). (* delta (unfold) then zeta (removes the let) *)
Eval cbv beta zeta delta [h] in (h 56 78). 
Eval cbv  beta zeta delta [h] in (h 56 78). 

Definition Z_bin : Set := Z->Z->Z.

Check (fun z0 z1:Z => let d:= z0 - z1 in d * d).
Definition Zdist2 : Z_bin :=
  fun z0 z1: Z => let d:= z0 - z1 in d * d.

Check Zdist2.
Check nat->nat.
Check (nat->nat):Type.  (* upcast *)





