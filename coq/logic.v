Set Implicit Arguments.

Inductive P (V : Set) : Set :=
  | Belong : V -> V -> P V
  | Bot    : P V
  | Imply  : P V -> P V -> P V 
  | Forall : V -> P V -> P V.


Fixpoint subst {V:Set}{W:Set} (sig: V -> W) (phi: P V) : P W :=
  match phi with
    | Belong x y        => Belong (sig x) (sig y)
    | Bot _             => Bot _
    | Imply f1 f2       => Imply (subst sig f1) (subst sig f2) 
    | Forall x f1       => Forall (sig x) (subst sig f1)
  end.

Definition compose {U:Set}{V:Set}{W:Set}(tau:U->V)(sig:V->W): U->W :=
  fun x => sig (tau x).

Lemma subst_compose: forall U V W: Set, 
  forall tau: U->V, forall sig: V->W, forall phi: P U, 
  subst (compose tau sig) phi = compose (subst tau) (subst sig) phi.

  Proof.
  intros U V W tau sig phi. elim phi.

  clear phi. intros x y. unfold subst at 1. unfold compose at 3.
  unfold subst at 2. unfold subst at 1. unfold compose. reflexivity.

  clear phi. unfold subst at 1. unfold compose. unfold subst at 2. 
  unfold subst. reflexivity.

  clear phi. intros p1 H1 p2 H2. unfold subst at 1.
  fold (subst (compose tau sig) p1). fold (subst (compose tau sig) p2).
  unfold compose at 3. unfold subst at 4. 
  fold (subst tau p1). fold (subst tau p2). unfold subst at 3.
  fold (subst sig (subst tau p1)). fold (subst sig (subst tau p2)).
  fold (compose (subst tau) (subst sig) p1).
  fold (compose (subst tau) (subst sig) p2).
  rewrite <- H1. rewrite <- H2. reflexivity.

  clear phi. intros x p1 H1. unfold subst at 1. 
  fold (subst (compose tau sig) p1).

Show.

