Declare Scope ZF_Core_Pipe_scope.
Open    Scope ZF_Core_Pipe_scope.

Class Pipe (v w:Type) := { pipe : v -> w -> v }.

Notation "a :|: b" := (pipe a b)
  (at level 13, left associativity) : ZF_Core_Pipe_scope.

