Require Import Logic.Rel.R. 

(* Reflexive predicate on Rel a                                                 *)
Definition reflexive (a:Type) (r:Rel a) : Prop := forall (x:a), 
    r x x.

Arguments reflexive {a} _.

(* Symmetric predicate on Rel a                                                 *)
Definition symmetric (a:Type) (r:Rel a) : Prop := forall (x y:a), 
    r x y -> r y x.

Arguments symmetric {a} _.

(* Transitive predicate on Rel a                                                *)
Definition transitive (a:Type) (r:Rel a) : Prop := forall (x y z:a), 
    r x y -> r y z -> r x z.

Arguments transitive {a} _.

Definition antisymmetric (a:Type) (r:Rel a) : Prop := forall (x y:a),
    r x y -> r y x -> x = y.

Arguments antisymmetric {a} _.

(* Equivalence predicate on Rel a                                               *)
Definition equivalence (a:Type) (r:Rel a) : Prop := 
    reflexive r /\ symmetric r /\ transitive r.

Arguments equivalence {a} _.

Definition partial_order (a:Type) (r:Rel a) : Prop :=
    reflexive r /\ antisymmetric r /\ transitive r.

Arguments partial_order {a} _.
