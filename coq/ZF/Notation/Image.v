Declare Scope ZF_Core_Image_scope.
Open    Scope ZF_Core_Image_scope.

Class Image (v w:Type) := { image : v -> w -> w }.

Notation "F :[ P ]:" := (image F P)
  (at level 0, no associativity) : ZF_Core_Image_scope.

