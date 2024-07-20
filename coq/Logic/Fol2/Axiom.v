Require Import Logic.Class.Eq.

Require Import Logic.Fol.Free.
Require Import Logic.Fol.Syntax.

(* Predicate determining whether a proposition is a set theoretic axiom         *)
(* This is just a stub for now, no set theoretic axiom is defined for now       *)
Definition IsAxiom (v:Type) (e:Eq v) (p:P v) : Prop := False.

Arguments IsAxiom {v} {e}.

Lemma axiomsClosed : forall (v:Type) (e:Eq v) (p:P v), IsAxiom p -> Fr p = nil.
Proof.
  intros v e p HAx. contradiction.
Qed.
