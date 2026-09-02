Require Import JMeq.

Check JMeq_eq.

(*
forall (A : Type) (x y : A), JMeq x y -> x = y
*)

Check JMeq_ind.

(*
forall (A : Type) (x : A) (P : A -> Prop),
       P x -> forall y : A, JMeq x y -> P y
*)
