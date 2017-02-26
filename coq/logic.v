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
  subst (compose tau sig) = compose (subst tau) (subst sig).

  Proof.

