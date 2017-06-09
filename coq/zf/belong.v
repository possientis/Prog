Require Import set.

(************************************************************************)
(*                  The set membership relation                         *)
(************************************************************************)

Parameter belong: set -> set -> Prop.

Notation "a : b" := (belong a b) (at level 10) : core_scope.

