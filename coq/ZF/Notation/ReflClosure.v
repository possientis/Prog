Declare Scope ZF_Notation_ReflClosure_scope.
Open    Scope ZF_Notation_ReflClosure_scope.

Class ReflClosure (v:Type) := { reflClosure : v -> v }.

Notation "R ^:=:" := (reflClosure R)
  (at level 0, no associativity) : ZF_Notation_ReflClosure_scope.

