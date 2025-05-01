Declare Scope ZF_Notation_Image_scope.
Open    Scope ZF_Notation_Image_scope.

Class Image (v w:Type) := { image : v -> w -> w }.

Notation "F :[ P ]:" := (image F P)
  (at level 0, no associativity) : ZF_Notation_Image_scope.

