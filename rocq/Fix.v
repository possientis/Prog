Inductive TreeF (a:Type) : Type :=
| Leaf : TreeF a
| Node : TreeF a -> a -> TreeF a -> TreeF a
.

Inductive Tree : Type :=
| mkTree : TreeF Tree -> Tree
.

CoInductive coTreeF (a:Type) : Type :=
| coNode : coTreeF a -> a -> coTreeF a -> coTreeF a
.

CoInductive coTree : Type :=
| mkCoTree : coTreeF coTree -> coTree
.

Fail Inductive Fix (f:Type -> Type) : Type :=
| mkFix : f (Fix f) -> Fix f
.

Fail CoInductive Fix (f:Type -> Type) : Type :=
| mkFix : f (Fix f) -> Fix f
.

