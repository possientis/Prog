Require Import ZF.Set.

(* Predicate over classes: a class has at least one element.                    *)
Definition Exists (P:U -> Prop) : Prop := exists x, P x.

(* Predicate over classes: a class has no more than one element.                *)
Definition Unique (P:U -> Prop) : Prop := forall a b, P a -> P b -> a = b.

(* When a class has a unique element, we can define such an element.            *)
Axiom define : forall (P:U -> Prop), Exists P -> Unique P -> U.

(* The set defined by a class with a unique element belongs to the class.       *)
Axiom DefineSatisfy: forall (P:U -> Prop) (p:Exists P) (q:Unique P),
    P(define P p q).

(* The set defined by a class with a unique element is unique.                  *)
Proposition DefineUnique : forall (P:U -> Prop) (p:Exists P) (q:Unique P),
  forall x, P x -> x = define P p q.
Proof.
  intros P p q x Hx. apply q.
  - apply Hx.
  - apply DefineSatisfy.
Qed.

(* The set defined by a class with a unique element is proof-irrelevant.        *)
Proposition DefineProof : forall (P:U -> Prop) (p p':Exists P) (q q':Unique P),
  define P p q = define P p' q'.
Proof.
  intros P p p' q q'. apply DefineUnique, DefineSatisfy.
Qed.

(* Any proposition involving define can be rewritten without it.                *)
Proposition DefineElim : forall (P Q:U -> Prop) (p: Exists P) (q: Unique P),
  Q(define P p q) <-> forall x, P x -> Q x.
Proof.
  intros P Q p q. split.
  - intros H1 x H2.
    assert (x = define P p q) as H3.
      { apply DefineUnique, H2. }
    rewrite H3. apply H1.
  - intros H1. apply H1, DefineSatisfy.
Qed.
