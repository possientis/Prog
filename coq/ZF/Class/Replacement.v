Require Import ZF.Axiom.Replacement.
Require Import ZF.Class.Core.
Require Import ZF.Class.Functional.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.

(* A version of the replacement axiom which does not make use of binary class.  *)
Theorem Replacement : forall (F:Class), Functional F ->
  forall a, exists b, forall y, y :< b <-> exists x, x :< a /\ F :(x,y):.
Proof.
  (* Let F be an arbitrary class. *)
  intros F.

  (* We assume that F is functional. *)
  intros H1. assert (Functional F) as A. apply H1. clear A.

  (* Let a be an arbitrary set. *)
  intros a.

  (* We need to show the existence of a set be with the right property. *)
  assert (exists b, forall y,y :< b <-> exists x, x :< a /\ F:(x,y):) as A.
  2: apply A.

  (* Consider the binary predicate G y x = F (x,y). *)
  remember (fun x y => F :(x,y):) as G eqn:EG.

  (* We claim that G is functional. *)
  assert (Replacement.Functional G) as H2. {
    intros x y z H2 H3. rewrite EG in H2. rewrite EG in H3.
    revert H2 H3. apply H1.
  }

  (* We can apply the replacement axiom to G and the set a. *)
  remember (Replacement.Replacement G H2 a) as H3 eqn:E. clear E.

  (* Which gives us the existence of a set b. *)
  destruct H3 as [b H3].

  (* We claim that b has the desired property, *)
  exists b.

  intros y. split; intros H4.
  - apply H3 in H4. destruct H4 as [x [H4 H5]]. exists x. split.
    1: assumption. rewrite EG in H5. assumption.
  - destruct H4 as [x [H4 H5]]. apply H3. exists x. split.
    1: assumption. rewrite EG. assumption.
Qed.
