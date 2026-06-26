Require Import ZF.Class.Equiv.
Require Import ZF.Class.Order.Irreflexive.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Order.Isom.
Require Import ZF.Set.Order.Transport.
Require Import ZF.Set.Relation.Bij.
Require Import ZF.Set.Relation.Converse.
Require Import ZF.Set.Relation.Eval.

Module COI := ZF.Class.Order.Irreflexive.

(* Predicate expressing the fact that r is an irreflexive set on a.             *)
Definition Irreflexive (r a:U) : Prop := forall (x:U), x :< a -> ~ :(x,x): :< r.

(* If the sets form an irreflexive pair, then so do the classes.                *)
Proposition ToClass : forall (r a:U),
  Irreflexive r a -> COI.Irreflexive (toClass r) (toClass a).
Proof.
  intros r a H1. assumption.
Qed.

(* If the classes form an irreflexive pair, then so do the sets.                *)
Proposition FromClass : forall (r a:U),
  COI.Irreflexive (toClass r) (toClass a) -> Irreflexive r a.
Proof.
  intros r a H1. assumption.
Qed.

(* Irreflexivity on a restricts to irreflexivity on any subset b.               *)
Proposition InclCompat : forall (r a b:U),
  b :<=: a -> Irreflexive r a -> Irreflexive r b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  (* Elements of b are elements of a, so the larger-domain property applies.    *)
  intros r a b H1 H2 x H3. apply H2, H1. assumption.
Qed.

(* Irreflexivity is preserved and reflected by order isomorphisms.              *)
Proposition IsomCompat : forall (f r s a b:U),
  Isom f r s a b -> Irreflexive r a <-> Irreflexive s b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  (* It is sufficient to prove one implication.                                 *)
  assert (forall (f r s a b:U),
    Isom f r s a b -> Irreflexive r a -> Irreflexive s b) as L. {
    intros f r s a b H1 H2 y H3 H4.
    assert (H5 := H1). destruct H5 as [H5 H6].
    remember (eval (f^:-1:) y) as x eqn:H7.
    assert (x :< a) as H8. { rewrite H7.
      apply Bij.ConverseEvalIsInDomain with b; assumption. }
    assert (y = f!x) as H9. { rewrite H7. symmetry.
      apply Bij.EvalOfConverseEval with a b; assumption. }
    assert (:(x,x): :< r) as H10. {
      apply H6; try assumption. rewrite <- H9. assumption. }
    revert H10. apply H2. assumption.
  }
  (* The converse direction follows from applying the same implication to f^-1. *)
  intros f r s a b H1. split.
  - apply L with f. assumption.
  - apply L with f^:-1:, Isom.Converse. assumption.
Qed.

(* Irreflexivity is preserved under transport by a bijection.                   *)
Proposition Transport : forall (f r s a b:U),
  s = transport f r a ->
  Bij f a b           ->
  Irreflexive r a     ->
  Irreflexive s b.
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)
  intros f r s a b H1 H2 H3 y H4 H5.
  apply (Bij.RangeCharac f a b) in H4. 2: assumption.
  destruct H4 as [x [H4 H6]].
  rewrite <- H6 in H5. rewrite H1 in H5.
  apply (Transport.Charac2f f r a b) in H5. 2-4: assumption.
  revert H5. apply H3. assumption.
Qed.
