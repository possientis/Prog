Declare Scope ZF_Notation_Pipe_scope.
Open    Scope ZF_Notation_Pipe_scope.

Class Pipe (v w u:Type) := { pipe : v -> w -> u }.

Notation "a :|: b" := (pipe a b)
  (at level 36, left associativity) : ZF_Notation_Pipe_scope.

