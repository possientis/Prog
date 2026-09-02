Inductive sig (A:Set)(P:A->Prop) : Set :=
  | exist : forall x:A, P x -> sig A P.


