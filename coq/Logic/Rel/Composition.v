Require Import Logic.Axiom.Extensionality.

Require Import Logic.Rel.R.

(* Composition operator.                                                        *)
Definition comp (a b c:Type) (s:R b c) (r:R a b) : R a c :=
    fun (x:a) (z:c) => exists (y:b), r x y /\ s y z.

Arguments comp {a} {b} {c}.


Notation "s ; r" := (comp s r) 
    (at level 60, right associativity) : Rel_Composition_scope.

Open Scope Rel_Composition_scope.

(* associativity law.                                                           *)
Lemma comp_assoc : forall (a b c d:Type) (r:R a b) (s:R b c) (t:R c d),
    (t ; s) ; r = t ; (s ; r).
Proof.
    intros a b c d r s t. apply Ext. intros x y. unfold comp. split.
    - intros [x' [H1 [y' [H2 H3]]]]. exists y'. split.
        + exists x'. split; assumption.
        + assumption.
    - intros [y' [[x' [H1 H2]] H3]]. exists x'. split.
        + assumption.
        + exists y'. split; assumption.
Qed.


