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

  clear phi. intros x y. 
    unfold subst at 1. unfold compose at 3.
    unfold subst at 2. unfold subst at 1. unfold compose. 
  reflexivity.

  clear phi. 
    unfold subst at 1. unfold compose. unfold subst at 2. 
    unfold subst. 
  reflexivity.

  clear phi. intros p1 H1 p2 H2. 
    unfold subst at 1.
    fold (subst (compose tau sig) p1). 
    fold (subst (compose tau sig) p2).
    unfold compose at 3. unfold subst at 4. 
    fold (subst tau p1). fold (subst tau p2). 
    unfold subst at 3.
    fold (subst sig (subst tau p1)). 
    fold (subst sig (subst tau p2)).
    rewrite H1. unfold compose at 1.
    rewrite H2. unfold compose at 1. 
  reflexivity.

  clear phi. intros x p1 H1. 
    unfold subst at 1. 
    fold (subst (compose tau sig) p1).
    unfold compose at 1. rewrite H1. unfold compose at 1.
    unfold compose. unfold subst at 4. fold (subst tau p1).
    unfold subst at 3. fold (subst sig (subst tau p1)).
  reflexivity.
Qed.

Definition identity {V:Set} (phi: V) := phi.

Lemma subst_identity: forall V: Set, forall phi: P V,
  subst identity phi = identity phi.
Proof.
  intros V phi. elim phi.

  clear phi. intros x y.
    unfold subst. unfold identity.
  reflexivity.

  clear phi. 
    unfold subst. unfold identity.
  reflexivity.

  clear phi. intros p1 H1 p2 H2.
    unfold subst. fold (subst identity p1). fold (subst identity p2).
    rewrite H1, H2. unfold identity.
  reflexivity.

  clear phi. intros x p1 H1. 
    unfold subst. fold (subst identity p1).
    rewrite H1. unfold identity.
  reflexivity.
Qed. 



