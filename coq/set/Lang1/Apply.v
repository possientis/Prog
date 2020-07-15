Require Import Utils.Replace.

Require Import Lang1.Syntax.

(* A formula with a free variable could be viewed as a predicate. Viewed as a   *)
(* predicate a formula may need to be 'evaluated' at another variable, and this *)
(* evaluation corresponds to a variable substitution. In the following, we      *)
(* formalize this evaluation by substituting the variable '0' by the argument n *)
(* This choice of variable '0' is arbitrary, but having this default choice     *)
(* leads to simpler syntax as there is no need to spell out which variable is   *)
(* being substituted. There is nothing deep here, as we are just creating a new *)
(* formula from an old one. The ability to apply a formula viewed as predicate  *)
(* to variables in particularly important for two variables as this is needed   *)
(* to express the axiom schema of replacement.                                  *)

Definition apply (p:Formula) (n:nat) : Formula := fmap (replace 0 n) p.

Notation "p $ n" := (apply p n) (at level 60, right associativity) : set_scope.
