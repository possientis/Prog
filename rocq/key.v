Module Type KEY.
  Parameter A : Set.
  Parameter eqdec: forall a b:A, {a = b}+{a <> b}.
End KEY.


