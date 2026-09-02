Section FreeUniversalAlgebraFOL.
  Variable V : Set.

  Inductive P : Set :=
  | Belong : V -> V -> P
  | Bot    : P
  | Imply  : P -> P -> P
  | Forall : V -> P -> P.

End FreeUniversalAlgebraFOL.


Section SubstitutionMapping.
  Variable V : Set.
  Variable W : Set.
  Variable sig : V -> W.

  Fixpoint Subst (phi : P V) : P W :=
    match phi with
      | Belong x y        => (Belong W)(sig x)(sig y)
      | Bot               => (Bot W)
      | Imply phi_1 phi_2 => (Imply W)(Subst phi_1)(Subst phi_2)
      | Forall x phi_1    => (Forall W)(sig x)(Subst phi_1)
    end.
End SubstitutionMapping.

Section Composition.
  Variables U V W: Set.

  Definition compose (tau: U->V) (sig: V->W) : U->W :=
    fun x => sig (tau x).
End Composition.

Lemma subst_compose: forall U V W:Set, forall tau:U->V, forall sig: V->W, forall
phi: P U, Subst U W (compose U V W tau sig) phi = 
  compose (P U) (P V) (P W) (Subst U V tau) (Subst V W sig) phi. 
  induction phi.
  simpl.
  unfold compose.
  unfold Subst.
  reflexivity.
  simpl.
  unfold compose.
  unfold Subst.
  reflexivity.
  unfold compose at 1.
  simpl.

 








