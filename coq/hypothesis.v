(* Hypothesis is a synonym of Variable *)
(* axiom parameter variable hypothesis *)

Parameter A : Set. (* like Variable but at global level *)
Parameter CH: Prop.
Axiom continuum: CH.

Section try.
  Variable B : Set. (* local level *)
  Variable b : B.
  Variable Q : Prop.
  Variable P : Prop.
  Variable R : Prop.
  Hypothesis hyp1 : Q.
  Hypothesis hyp2 : P.
  Variable   hyp3 : R. (* hyp1 hyp2 hyp3 are proofs of Q P R respectively*)
