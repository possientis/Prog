Declare Scope ZF_Core_Product_scope.
Open    Scope ZF_Core_Product_scope.

Class Product (v:Type) := { product : v -> v -> v }.

Notation "a :x: b" := (product a b)
  (at level 11, right associativity) : ZF_Core_Product_scope.


