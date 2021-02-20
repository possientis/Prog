(* A proposition is (computationally) decidable                                 *)
Definition Dec (A:Prop) : Type := {A} + {~A}.

(* A predicate is (computationally) decidable                                    *)
Definition pDec (a:Type) (p:a -> Prop) : Type := forall (x:a), Dec (p x).

Arguments pDec {a}.

(* Two-fold decidable predicates                                                *)
Definition pDec2 (a b:Type) (p:a -> b -> Prop) := 
    forall (x:a) (y:b), Dec (p x y).

Arguments pDec2 {a} {b}.

Lemma pDec2Dec : forall (a b:Type) (p:a -> b ->Prop) (x:a),
    pDec2 p -> pDec (p x).
Proof.
    intros a b p x H1 y. apply H1.
Defined.

Definition DeciderOf (a:Type) (p:a -> Prop) (f:a -> bool) : Prop :=
    forall (x:a), p x <-> f x = true.

Arguments DeciderOf {a}.

Definition Decidable (a:Type) (p:a -> Prop) : Prop :=
    exists (f:a -> bool), DeciderOf p f.

Arguments Decidable {a}.

Lemma pDecDecidable : forall (a:Type) (p:a -> Prop),
    pDec p -> Decidable p.
Proof.
    intros a p q. remember (fun x => 
        match (q x) with
        | left _    => true
        | right _   => false
        end) as f eqn:E.
    exists f. intros x. split; intros H1.
    - rewrite E. destruct (q x) as [H2|H2].
        + reflexivity.
        + apply H2 in H1. contradiction.
    - rewrite E in H1. destruct (q x) as [H2|H2].
        + assumption.
        + inversion H1.
Qed.

