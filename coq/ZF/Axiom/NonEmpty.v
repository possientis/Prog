Require Import ZF.Set.

(* This axiom is not necessary as the axiom of infinity also asserts the        *)
(* the existence of at least one set. However, it allows us to define the empty *)
(* set early and rewrite more concisely the axiom of infinity later.            *)
Axiom NonEmptyUniverse : exists (x:U), True.


