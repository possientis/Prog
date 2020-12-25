(* A proposition is (computationally) decidable                                 *)
Definition Dec (A:Prop) : Type := {A} + {~A}.

(* a predicate is (comptationally) decidable                                    *)
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
