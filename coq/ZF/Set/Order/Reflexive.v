Require Import ZF.Class.Equiv.
Require Import ZF.Class.Order.Reflexive.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Order.Isom.
Require Import ZF.Set.Order.Transport.
Require Import ZF.Set.Relation.Bij.
Require Import ZF.Set.Relation.Converse.
Require Import ZF.Set.Relation.Eval.

Module COR := ZF.Class.Order.Reflexive.

(* Predicate expressing the fact that r is a reflexive set on a.                *)
Definition Reflexive (r a:U) : Prop := forall (x:U), x :< a -> :(x,x): :< r.

(* If the sets form a reflexive pair, then so do the classes.                   *)
Proposition ToClass : forall (r a:U),
  Reflexive r a -> COR.Reflexive (toClass r) (toClass a).
Proof.
  intros r a H1. assumption.
Qed.

(* If the classes form a reflexive pair, then so do the sets.                   *)
Proposition FromClass : forall (r a:U),
  COR.Reflexive (toClass r) (toClass a) -> Reflexive r a.
Proof.
  intros r a H1. assumption.
Qed.

(* Reflexivity on a restricts to reflexivity on any subset b.                   *)
Proposition InclCompat : forall (r a b:U),
  b :<=: a -> Reflexive r a -> Reflexive r b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  (* Elements of b are elements of a, so the larger-domain property applies.    *)
  intros r a b H1 H2 x H3. apply H2, H1. assumption.
Qed.

(* Reflexivity is preserved and reflected by order isomorphisms.                *)
Proposition IsomCompat : forall (f r s a b:U),
  Isom f r s a b -> Reflexive r a <-> Reflexive s b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  (* It is sufficient to prove one implication.                                 *)
  assert (forall (f r s a b:U),
    Isom f r s a b -> Reflexive r a -> Reflexive s b) as L. {
    intros f r s a b H1 H2 y H3.
    assert (H4 := H1). destruct H4 as [H4 H5].
    remember (f^:-1:!y) as x eqn:H6.
    assert (x :< a) as H7. { rewrite H6.
      apply Bij.ConverseEvalIsInDomain with b; assumption. }
    assert (y = f!x) as H8. { rewrite H6. symmetry.
      apply Bij.EvalOfConverseEval with a b; assumption. }
    rewrite H8. apply H5; try assumption. apply H2. assumption.
  }
  (* The converse direction follows from applying the same implication to f^-1. *)
  intros f r s a b H1. split.
  - apply L with f. assumption.
  - apply L with f^:-1:, Isom.Converse. assumption.
Qed.

(* Reflexivity is preserved under transport by a bijection.                     *)
Proposition Transport : forall (f r s a b:U),
  s = transport f r a ->
  Bij f a b           ->
  Reflexive r a       ->
  Reflexive s b.
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)
  intros f r s a b H1 H2 H3 y H4.
  apply (Bij.RangeCharac f a b) in H4. 2: assumption.
  destruct H4 as [x [H4 H5]].
  rewrite <- H5. rewrite H1.
  apply (Transport.Charac2f f r a b). 1-3: assumption. apply H3. assumption.
Qed.

