Require Import ZF.Class.Equiv.
Require Import ZF.Set.Core.

(* Predicate over classes: a class has at least one element.                    *)
Definition Exists (A:Class) : Prop := exists x, A x.

(* Predicate over classes: a class has no more than one element.                *)
Definition Unique (A:Class) : Prop := forall a b, A a -> A b -> a = b.

(* When a class has a unique element, we can define such an element.            *)
Axiom define : forall (A:Class), Exists A -> Unique A -> U.

(* The set defined by a class with a unique element belongs to the class.       *)
Axiom IsIn: forall (A:Class) (p:Exists A) (q:Unique A), A (define A p q).

(* The set defined by a class with a unique element is unique.                  *)
Proposition IsUnique : forall (A:Class) (p:Exists A) (q:Unique A),
  forall x, A x -> x = define A p q.
Proof.
  intros A p q x H1. apply q.
  - apply H1.
  - apply IsIn.
Qed.

(* Two equivalent classes define the same set.                                  *)
Proposition EquivCompat : forall (A B:Class),
  forall (p:Exists A) (q:Unique A),
  forall (p':Exists B) (q':Unique B),
    A :~: B  ->
    define A p q = define B p' q'.
Proof.
  intros A B p q p' q' H1. apply IsUnique, H1, IsIn.
Qed.

(* The set defined by a class with a unique element is proof-irrelevant.        *)
Proposition ProofIrrelevant : forall (A:Class) (p p':Exists A) (q q':Unique A),
  define A p q = define A p' q'.
Proof.
  intros A p p' q q'. apply IsUnique, IsIn.
Qed.

(* Any proposition involving define can be rewritten without it.                *)
Proposition Elim : forall (A B:Class) (p: Exists A) (q: Unique A),
  B(define A p q) <-> forall x, A x -> B x.
Proof.
  intros A B p q. split.
  - intros H1 x H2.
    assert (x = define A p q) as H3. { apply IsUnique, H2. }
    rewrite H3. apply H1.
  - intros H1. apply H1, IsIn.
Qed.

