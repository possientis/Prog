Require Import ZF.Class.Cardinal.Aleph.
Require Import ZF.Class.Equiv.
Require Import ZF.Set.Core.
Require Import ZF.Set.Relation.EvalOfClass.

Module CCA := ZF.Class.Cardinal.Aleph.

(* The isomorphism between the ordinals and infinite cardinals evaluated at a.  *)
Definition aleph (a:U) : U := CCA.Aleph!a.
