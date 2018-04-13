Require Import Setoids.


Record Category : Type :=
  { Arr     : Setoid
  ; src     : Arr ~> Arr
  ; tgt     : Arr ~> Arr
  ; cmp     : Arr -> (Arr ==> Arr)
  }
  .
