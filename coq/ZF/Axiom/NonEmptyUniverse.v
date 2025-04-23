Require Import ZF.Set.Core.

(* This axiom is not necessary as the axiom of infinity also asserts the        *)
(* the existence of at least one set. However, it allows us to define the empty *)
(* set early and rewrite the axiom of infinity more concisely later.            *)
Axiom NonEmptyUniverse : exists (x:U), True.
