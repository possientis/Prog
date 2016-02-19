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

  Hypothesis EM : forall A:Prop, A\/~A.

  Lemma drinker : exists x:D, P x -> forall x:D, P x.
    clear R.
    elim(EM(exists x:D, ~P x)).
    intro Non_drinker.
    elim Non_drinker.
    intro Tom.
    intro Tom_does_not_drink.
    exists Tom.
    intro Tom_drinks.
    absurd (P Tom).
    assumption.
    assumption.
    intro Non_nondrinker.
    exists d.
    intro d_drinks.
    intro Dick.
    elim (EM (P Dick)).
    intro Dick_drinks.
    assumption.
    intro Dick_does_not_drink.
    absurd (exists x, ~ P x).
    assumption.
    exists Dick.
    assumption.
  Qed.
End Predicate_calculus.

Check drinker.

Section Predicate_Calculus.
  Variables P Q : nat -> Prop.
  Variable R : nat -> nat -> Prop.

  Lemma PQR : forall x y : nat, (R x x -> P x -> Q x) -> P x -> R x y -> Q x.
    intros.
    generalize H0.
    cut(R x x).
    assumption.
  Abort.



 
