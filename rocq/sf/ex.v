(*
Inductive ex (a:Type) (P:a -> Prop) : Prop :=
| ex_intro : forall (x:a), P x -> ex a P
.

Arguments ex {a} _.
Arguments ex_intro {a} _ _ _.
*)
