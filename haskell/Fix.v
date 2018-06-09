CoInductive Fix (a:Type) : Type :=
| MkFix : (Fix a -> a) -> Fix a
.

