Require Import ZF.Class.Incl.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Order.Closed.
Require Import ZF.Class.Order.Induction.
Require Import ZF.Class.Order.WellFounded.
Require Import ZF.Class.Relation.Converse.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Order.InitSegment.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.FunctionOn.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.Restrict.

Require Import ZF.Notation.Eval.
Require Import ZF.Notation.Image.

Module CIN := ZF.Class.Incl.
Module CRC := ZF.Class.Relation.Converse.


(* The recursion class associated with R A F. In other words, when R is well    *)
(* founded on A, the unique function class G defined on A by the recursion:     *)
(* G(b) = F(G|initSegment R A b).                                               *)
Definition Recursion (R A F:Class) : Class := fun x => exists f a,
  x :< f                                                            /\
  toClass a :<=: A                                                  /\
  Closed R^:-1: (toClass a)                                         /\
  FunctionOn f a                                                    /\
  (forall b, b :< a -> f!b = F!(f:|:initSegment R A b)).

(* Binary predicate underlying the recursion class.                             *)
Definition K (R A F:Class) : U -> U -> Prop := fun f a =>
  toClass a :<=: A                                                  /\
  Closed R^:-1: (toClass a)                                         /\
  FunctionOn f a                                                    /\
  (forall b, b :< a-> f!b = F!(f:|:initSegment R A b)).

Proposition Charac2 : forall (R A F:Class) (x y:U),
  Recursion R A F :(x,y): <-> exists f a, :(x,y): :< f /\ K R A F f a.
Proof.
  intros R A F x y. split; intros [f [a [H1 H2]]];
  exists f, a; split; assumption.
Qed.

(* Two recursive functions coincide on their common domain.                     *)
Lemma Coincide : forall (R A F:Class) (f g a b:U),
  WellFounded R A                                         ->
  toClass a :<=: A                                        ->
  Closed R^:-1: (toClass a)                               ->
  a :<=: b                                                ->
  FunctionOn f a                                          ->
  FunctionOn g b                                          ->
  (forall x, x :< a -> f!x = F!(f:|:initSegment R A x))   ->
  (forall x, x :< a -> g!x = F!(g:|:initSegment R A x))   ->
  (forall x, x :< a -> f!x = g!x).
Proof.
  intros R A F f g a b H1 H2 H4 H6 H7 H8 H9 H10.
  assert (A :<=: A) as G1. { apply CIN.Refl. }
  remember (fun x => x :< a -> f!x = g!x) as B eqn:H12.
  assert (forall x, A x -> B x) as H13. {
    apply Induction.Induction with R. 1: assumption. rewrite H12.
    intros c H13 IH H14.
    assert (initSegment R A c :<=: a) as H15. {
      intros u H15.
      assert (R :(u,c):) as H16. {
        apply (InitSegment.IsLess R A A); assumption. }
      apply H4. exists c. split. 1: assumption.
      apply CRC.Charac2Rev. assumption. }
    assert (initSegment R A c :<=: b) as H16. {
      apply Incl.Tran with a; assumption. }
    assert (forall x, x :< initSegment R A c -> f!x = g!x) as H17. {
      intros x H17. apply IH. 1: assumption. apply H15. assumption. }
    assert (f:|:initSegment R A c = g :|: initSegment R A c) as H18. {
      apply FunctionOn.RestrictEqual with a b; assumption. }
    assert (f!c = F!(f:|:initSegment R A c)) as H19. {
      apply H9. assumption. }
    assert (g!c = F!(g:|:initSegment R A c)) as H20. {
      apply H10. assumption. }
    rewrite H19, H20, H18. reflexivity. }
    rewrite H12 in H13. intros x H14. apply H13. 2: assumption.
    apply H2. assumption.
Qed.

