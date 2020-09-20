Inductive Sig (a:Type) (p:a -> Type) : Type :=
| Ex : forall (x:a), p x -> Sig a p
.

Arguments Sig {a}.
Arguments Ex {a} {p}.

(* f is a decider for p                                                         *)
Definition Decider (a:Type) (f:a -> bool) (p:a -> Prop) : Prop :=
    forall (x:a), p x <-> f x = true.

Arguments Decider {a}.

Definition Decidable (a:Type) (p:a -> Prop) : Prop :=
    exists (f:a -> bool), Decider f p.

Arguments Decidable {a}.


(* f is a semi-decider for p                                                    *)
Definition SemiDecider (a:Type) (p:a -> Prop) (f:a -> nat -> bool) : Prop :=
    forall (x:a), p x <-> exists (n:nat), f x n = true.

Arguments SemiDecider {a}.

Definition SemiDecidable (a:Type) (p:a -> Prop) : Prop :=
    exists (f:a -> nat -> bool), SemiDecider p f.

Arguments SemiDecidable {a}.

Lemma L1 : forall (a:Type) (p:a -> Prop), Decidable p -> SemiDecidable p.
Proof.
    intros a p. unfold Decidable, SemiDecidable, Decider, SemiDecider.
    intros [f H1]. exists (fun x _ => f x). intros x. split.
    - intros H2. exists 0. apply H1. assumption.
    - intros [_ H2]. apply H1. assumption.
Qed.

Definition tsat (f: nat -> bool) : Prop := exists (n:nat), f n = true.

Lemma L2 : SemiDecidable tsat.
Proof.
    unfold SemiDecidable, tsat, SemiDecider. exists (fun g n => g n).
    intros f. split; auto.
Qed.

(* semi-decision type S(X) associated with proposition X.                       *)
Definition S (X:Prop) : Type := Sig (fun f => X <-> tsat f).

