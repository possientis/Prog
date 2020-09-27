(* Type of relations from a to b.                                               *)
Definition R (a b:Type) : Type := a -> b -> Prop.

Definition Rel (a:Type) : Type := R a a.
