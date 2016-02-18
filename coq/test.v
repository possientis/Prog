Section Predicate_calculus.
  Variable D : Set.
  Variable R : D -> D -> Prop.

  Section R_sym_trans.
  Hypothesis R_symmetric : forall x y : D, R x y -> R y x.
  Hypothesis R_transitive : forall x y z : D, R x y -> R y z -> R x z.

  Lemma refl_if : forall x : D, (exists y, R x y) -> R x x.
    intro x.
    intro Hxy.
    elim Hxy.
    intro y.
    intro Rxy.
    apply R_transitive with y.
    assumption.
    apply R_symmetric.
    assumption.
  Qed.
  End R_sym_trans.

  Variable P : D -> Prop.
  Variable d : D.

  (* this lemma is always true in classical first order logic *)
  (* however it cannot be proved in Coq unless we assume the *)
  (* domain of discourse D is non-empty *)
  Lemma weird : (forall x:D, P x) -> (exists x:D, P x).
    intro H.
    exists d. 
    apply H.
  Qed.
