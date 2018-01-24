Require Import list.
Require Import In.


Definition disjoint (a:Type) (l k:list a) : Prop :=
    forall x, In x l -> In x k -> False.

Arguments disjoint {a} _ _.

Inductive nodup (a:Type) : list a -> Prop :=
| nodup_nil  : nodup a []
| nodup_cons : forall (l:list a) (x:a), nodup a l -> ~In x l -> nodup a (x :: l)
.

Arguments nodup {a} _.


