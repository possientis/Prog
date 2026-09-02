(* NEXT: ===> Elem                                                              *)

Require Import Sets.Integers.
Import Nat.

Require Import Logic.Set.Set.
Require Import Logic.Set.Core.
Require Import Logic.Set.Order.

Declare Scope Set_Incl_scope.

(* At last we are able to define our inclusion relation on set. We previously   *)
(* observed that given xs and ys and a natural number m, provided m is no less  *)
(* than n = order xs + order ys, then all the inclusion statements in relation  *)
(* to m are equivalent to the one in relation to n. Hence we simply define the  *)
(* 'final' inclusion statement as the inclusion statement in relation to n.     *)
Definition incl (xs ys:set) : Prop :=
    let n := order xs + order ys in incl_n n xs ys.

(* This all important inclusion relation deserves an appropriate notation.      *)
Notation "x <= y" := (incl x y)
    (at level 70, no associativity) : Set_Incl_scope.


(* We shall need a few lemmas in order to prove that our relation has the       *)
(* desired properties. The following allows us to deduce an inclusion statement *)
(* for n from an inclusion statement proper, provided n is large enough.        *)
Lemma incl_incl_n : forall (xs ys:set) (n:nat),
    order xs + order ys <= n    ->
    incl xs ys                  ->
    incl_n n xs ys.
Proof.
    intros xs ys n H1 H2. unfold incl in H2.
    apply incl_n_m with (order xs + order ys).
    - apply le_n.
    - assumption.
    - assumption.
Qed.


(* This lemma allows us to go the other way, from an inclusion statement in     *)
(* relation to n, to an inclusion statement proper, provided n is large enough. *)
Lemma incl_n_incl : forall (xs ys:set) (n:nat),
    order xs + order ys <= n    ->
    incl_n n xs ys              ->
    incl xs ys.
Proof.
    intros xs ys n H1 H2. unfold incl.
    apply incl_n_m with n.
    - assumption.
    - apply le_n.
    - assumption.
Qed.

Open Scope Set_Incl_scope.

(* Nil is a subset of every set. Interestingly, this may look like our first    *)
(* theorem (as opposed to meta-theorem), i.e. our first provable proposition    *)
(* which can be expressed in the language of set theory itself. However, we     *)
(* have not made clear what 'the language of set theory' is at this stage.      *)
(* A core language of set theory would not have '<=' or 'Nil' as a primitive,   *)
(* and the statement 'Nil <= x' would need to be de-sugared in terms of core    *)
(* primitives.                                                                  *)
Lemma inclNil : forall (x:set), Nil <= x.
Proof.
    intros x. unfold incl. apply incl_n_Nil.
Qed.

(* The inclusion relation is reflexive.                                         *)
Lemma inclRefl : forall (x:set), x <= x.
Proof.
    intros x. apply incl_n_incl with (order x + order x).
    - apply le_n.
    - apply incl_n_refl. apply le_add_r.
Qed.
