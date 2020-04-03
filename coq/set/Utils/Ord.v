Class Ord (a:Type) :=
  { leq      : a -> a -> Prop
  ; leqDec   : forall (x y:a), { leq x y } + { ~ leq x y }
  ; eqDec    : forall (x y:a), { x = y }   + { ~ x = y }
  ; leqRefl  : forall (x:a), leq x x
  ; leqTrans : forall (x y z:a), leq x y -> leq y z -> leq x z
  ; leqAsym  : forall (x y:a), leq x y -> leq y x -> x = y
  ; leqTotal : forall (x y:a), leq x y \/ leq y x
  }.  

