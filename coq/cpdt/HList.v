Require Import List.
Import ListNotations.

Inductive HList (a:Type) (b:a -> Type) : list a -> Type :=
| HNil  : HList a b nil
| HCons : forall (x:a) (xs:list a), b x -> HList a b xs -> HList a b (x :: xs)
.

Arguments HList {a}.
Arguments HNil {a} {b}.
Arguments HCons {a} {b} {x} {xs}.


Inductive Elem (a:Type) (x:a) : list a -> Type :=
| HFirst : forall (xs:list a), Elem a x (x :: xs)
| HNext  : forall (xs:list a) (y:a), Elem a x xs -> Elem a x (y ::xs)
.

Arguments Elem {a}.
Arguments HFirst {a} {x} {xs}.
Arguments HNext  {a} {x} {xs} {y}.
