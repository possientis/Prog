(* Type of 'relations on a'                                                     *)
Definition Rel (a:Type) : Type := (a -> a -> Prop).

(* Reflexive predicate on Rel a                                                 *)
Definition isRefl (a:Type) (r:Rel a) : Prop := forall (x:a), 
    r x x.

Arguments isRefl {a} _.

(* Symmetric predicate on Rel a                                                 *)
Definition isSym (a:Type) (r:Rel a) : Prop := forall (x y:a), 
    r x y -> r y x.

Arguments isSym {a} _.

(* Transitive predicate on Rel a                                                *)
Definition isTran (a:Type) (r:Rel a) : Prop := forall (x y z:a), 
    r x y -> r y z -> r x z.

Arguments isTran {a} _.

(* Equivalence predicate on Rel a                                               *)
Definition isEquiv (a:Type) (r:Rel a) : Prop := isRefl r /\ isSym r /\ isTran r.

Arguments isEquiv {a} _.
