Require Import Logic.Axiom.Dec.

(* A proposition is weakly decidable                                            *)
Definition Wec (A:Prop) : Prop := A \/ ~A.


(* a predicate is weakly decidable                                              *)
Definition pWec (a:Type) (p:a -> Prop) : Prop := forall (x:a), Wec (p x).

Arguments pWec {a}.

(* Two-fold weakly decidable predicates                                         *)
Definition pWec2 (a b:Type) (p:a -> b -> Prop) := 
    forall (x:a) (y:b), Wec (p x y).

Arguments pWec2 {a} {b}.

Lemma pWec2Wec : forall (a b:Type) (p:a -> b -> Prop) (x:a),
    pWec2 p -> pWec (p x).
Proof.
    intros a b p x H1 y. apply H1.
Qed.

Lemma DecWec : forall (A:Prop), Dec A -> Wec A.
Proof.
    intros A [H1|H1]. 
    - left. assumption.
    - right. assumption.
Qed.

Lemma pDecWec : forall (a:Type) (p:a -> Prop), pDec p -> pWec p.
Proof.
    intros a p H1 x. apply DecWec. apply H1.
Qed.

