
Variable Term : Type.
Variable r : Term -> Term -> Prop.
Variable A : Term. (* type is not empty                                          *)

Notation "M ~> N" := (r M N) (at level 50).

Axiom WeakDec : forall (M N:Term), (M ~> N) \/ ~(M ~> N).

Definition confluence1 : Prop := forall (L M N:Term), 
    L ~> M -> L ~> N -> exists (P:Term), (M ~> P) /\ (N ~> P).

(* Seemingly as Stronger statement                                              *)
Definition confluence2 : Prop := forall (L M N:Term),
    exists (P:Term), L ~> M -> L ~> N -> (M ~> P) /\ (N ~> P).

Lemma L1 : confluence2 -> confluence1.
Proof.
    unfold confluence1, confluence2. intros H L M N H1 H2.
    destruct (H L M N) as [P H3]. exists P. apply H3; assumption.
Qed.

(* Term is not an empty type and relation is weakly decidable.                  *)
Lemma L2 : confluence1 -> confluence2.
Proof.
    unfold confluence1, confluence2. intros H L M N.
    destruct (WeakDec L M) as [H1|H1];
    destruct (WeakDec L N) as [H2|H2].
    - destruct (H L M N H1 H2) as [P [H3 H4]]. exists P. 
      intros. split; assumption.
    - exists A. intros H3 H4. apply H2 in H4. contradiction.
    - exists A. intros H3 H4. apply H1 in H3. contradiction.
    - exists A. intros H3 H4. apply H1 in H3. contradiction.
Qed.




