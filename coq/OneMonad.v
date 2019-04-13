Fail Inductive List (M : Type -> Type) (a : Type) : Type :=
| Nil  : List M a
| Cons : M a -> M (List M a) -> List M a
.


Fail Inductive NonStrictlyPos := 
| con : (NonStrictlyPos -> nat) -> NonStrictlyPos
.

Inductive StrictlyPos :=
| con : StrictlyPos -> (nat -> StrictlyPos) -> StrictlyPos
.

Fail Definition applyFun (t:NonStrictlyPos) : nat :=
    match t with
    | con f => f t
    end.

Fail Inductive Mu (a:Type) : Type :=
| mu : (Mu a -> a) -> Mu a
.

Definition Cont r a := (a -> r) -> r.

Fail Inductive ListC r a :=
| NilC : ListC r a
| ConsC: ((a -> r) -> r) -> ((ListC r a -> r) -> r) -> ListC r a
.

Fail Inductive Free f a :=
| pure   : a -> Free f a
| impure : f (Free f a) -> Free f a
.

Inductive Void :=.

Definition Zero (a:Type) : Type := Void.
Definition One  (a:Type) : Type := unit.

Inductive Const (b a: Type) : Type := 
| const : b -> Const b a
.

Fail Inductive FixF f := fixF : f (FixF f) -> FixF f.

Inductive Ext Shape (Pos:Shape -> Type) a :=
| ext : forall s, (Pos s -> a) -> Ext Shape Pos a
.

Arguments ext {Shape} {Pos} {a} _ _.

Definition ShapeOne := unit.
Definition PosOne (s:ShapeOne) := Void.
Definition ExtOne a := Ext ShapeOne PosOne a.
