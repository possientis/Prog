(* fails by default, will work with -impredicative-set option                   *)
Definition id : Set := forall (x:Set), x -> x.
