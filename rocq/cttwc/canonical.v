(* term : well-typed syntactic object                                           *)
(* closed: a term is closed if it has no free variables                         *)
(* normal: no futher reduction is possible                                      *)
(* canonical: both closed and normal                                            *)
(* In Coq, every canonical term is either:                                      *)
(*  1. a constructor                                                            *)
(*  2. a constructor applied to canonical terms                                 *)
(*  3. an abstraction obtained with 'fun' or 'fix'                              *)
(*  4. a function type obtained with '->' or 'forall'                           *)
(*  5. a universe (Prop, Type 0, Type 1, ...                                    *)

(* Every closed term reduces to a canonical term                                *)

(* values : semantic objects described though canonical terms                   *)
(* inhabitants of a type: canonical terms of the type                           *)

