(* NEXT: ===> Extensionality                                                    *)

Require Import Core.Set.
Require Import Core.Elem.

Open Scope set_scope.

(* There is one other crucially important relation on 'set' which we have not   *)
(* yet defined, namely that of equality. It is tempting to define equality      *)
(* simply as 'double inclusion'. However, if we assume that equality is not     *)
(* part of a core set theoretic language, but is instead defined in terms of    *)
(* core primitives, the definition we choose should make it obvious that if P   *)
(* is a predicate on sets expressed in the core language, then if two sets x y  *)
(* are deemed equal, the statement P x should be equivalent to the statement    *)
(* P y. For example, if x and y are deemed equal, the statements x :: z and     *)
(* and y :: z should be equivalent for all z. A definition of equality in terms *)
(* of 'double inclusion' would fail to make such equivalence obvious. As we     *)
(* shall see in the 'Extensionality' module, the definition of equality we      *)
(* adopt below is in fact equivalent to 'double inclusion'. However, the point  *)
(* is 'double inclusion' is not the right definition: if x and y are deemed     *)
(* equal, we don't simply want the equivalence 'z :: x <-> z :: y' to hold for  *)
(* all z, we also want the equivalence 'x :: z <-> y :: z'. For any predicate P *)
(* expressed in terms of :: and logical connectives, these two equivalences     *)
(* should ensure that P x <-> P y when x == y (this would need to be formalized *)
(* and proven). In short, for two sets to be equal, we need more than them      *)
(* having identical elements, we also need them to belong to the same sets.     *)
Definition equal (x y:set) : Prop :=
    (forall (z:set), z :: x <-> z :: y) 
 /\ (forall (z:set), x :: z <-> y :: z). 

Notation "x == y" := (equal x y) (at level 90) : set_scope.

(* Our equality relation is reflexive.                                          *)
Lemma equalRefl : forall (x:set), x == x.
Proof.
    intros x. split; intros z; split; intros H; assumption.
Qed.

(* Our equality relation is symmetric.                                          *)
Lemma equalSym : forall (x y:set), x == y -> y == x.
Proof.
    intros x y [H1 H2]. split; intros z; split; intros H.
    - apply H1. assumption.
    - apply H1. assumption.
    - apply H2. assumption.
    - apply H2. assumption.
Qed.

(* Our equality relation is transitive                                          *)
Lemma equalTrans : forall (x y z:set), x == y -> y == z -> x == z.
Proof.
    intros x y z [H1 H2] [H3 H4]. split; intro t; split; intros H.
    - apply H3, H1. assumption.
    - apply H1, H3. assumption.
    - apply H4, H2. assumption.
    - apply H2, H4. assumption.
Qed.

(* These immediate consequences of equality are sometimes useful in proofs      *)
Lemma equal_l : forall (x y z:set), x == y -> x :: z -> y :: z.
Proof.
    intros x y z [H1 H2] H. apply H2. assumption.
Qed.

Lemma equal_r : forall (x y z:set), x == y -> z :: x -> z :: y.
Proof.
    intros x y z [H1 H2] H. apply H1. assumption.
Qed.

Lemma equal_lr : forall (x x' y y':set), x == x' -> y == y' -> x :: y -> x' :: y'.
Proof.
    intros x x' y y' Hx Hy H. apply equal_l with x.
    - assumption.
    - apply equal_r with y; assumption.
Qed.

