Require Import ZF.Class.Equiv.
Require Import ZF.Class.Order.Founded.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Order.Isom.
Require Import ZF.Set.Order.Minimal.
Require Import ZF.Set.Order.Transport.
Require Import ZF.Set.Relation.Bij.

Module COF := ZF.Class.Order.Founded.

(* Predicate expressing the fact that r is a founded set on a.                  *)
Definition Founded (r a:U) : Prop := forall b,
  b :<=: a                  ->
  b <> :0:                  ->
  exists x, Minimal r b x.

(* If the sets form a founded pair, then so do the classes.                     *)
Proposition ToClass : forall (r a:U),
  Founded r a -> COF.Founded (toClass r) (toClass a).
Proof.
  intros r a H1. assumption.
Qed.

(* If the classes form a founded pair, then so do the sets.                     *)
Proposition FromClass : forall (r a:U),
  COF.Founded (toClass r) (toClass a) -> Founded r a.
Proof.
  intros r a H1. assumption.
Qed.

(* Foundedness on a restricts to foundedness on any subset b.                   *)
Proposition InclCompat : forall (r a b:U),
  b :<=: a -> Founded r a -> Founded r b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  (* Every non-empty subset of b is also a non-empty subset of a.               *)
  intros r a b H1 H2 c H3 H4. apply H2. 2: assumption.
  apply Incl.Tran with b; assumption.
Qed.

(* Foundedness is preserved under transport by a bijection.                     *)
Proposition Transport : forall (f r s a b:U),
  s = transport f r a ->
  Bij f a b           ->
  Founded r a         ->
  Founded s b.
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)
  intros f r s a b H1 H2 H3. apply FromClass.
  apply (COF.IsomCompat (toClass f) (toClass r) (toClass s) (toClass a) (toClass b)).
  - apply Isom.ToClass. apply Isom.Transport; assumption.
  - apply ToClass. assumption.
Qed.
