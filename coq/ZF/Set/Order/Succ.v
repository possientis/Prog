Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Order.FinalSegment.
Require Import ZF.Class.Order.Maximal.
Require Import ZF.Class.Order.Minimal.
Require Import ZF.Class.Order.Succ.
Require Import ZF.Class.Order.Total.
Require Import ZF.Class.Order.WellFoundedWellOrd.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Truncate.

Module COS := ZF.Class.Order.Succ.

(* The successor in the ordered class (A,R) of a set a.                         *)
Definition succ (R A:Class) (a:U) : U := truncate (COS.succ R A a).

Proposition ToClass : forall (R A:Class) (a:U),
  WellFoundedWellOrd R A                    ->
  A a                                       ->
  toClass (succ R A a) :~: COS.succ R A a.
Proof.
  intros R A a H1 H2.
  apply Truncate.WhenSmall, COS.IsSmall; assumption.
Qed.

Proposition Charac : forall (R A:Class) (a b:U),
  WellFoundedWellOrd R A                        ->
  A a                                           ->
  ~ Maximal R A a                               ->
  succ R A a = b                               <->
  A b                                           /\
  R :(a,b):                                     /\
  forall x, A x -> R :(a,x): -> ~ R :(x,b):.
Proof.
  intros R A a b H1 H2 H3. split; intros H4.
  - apply COS.WhenNotMaximal in H3; try assumption.
    destruct H3 as [c [H3 [H5 [H6 H7]]]].
    assert (c = b) as H8. {
      rewrite <- H4. apply EqualToClass.
      apply Equiv.Tran with (COS.succ R A a). 1: assumption.
      apply Equiv.Sym, ToClass; assumption. }
    rewrite <- H8. split. 1: assumption. split; assumption.
  - apply COS.WhenNotMaximal in H3; try assumption.
    destruct H3 as [c [H3 [H5 [H6 H7]]]].
    destruct H4 as [H4 [H8 H9]].
    remember (finalSegment R A a) as B eqn:H10.
    assert (Minimal R B b) as H11. {
      split.
      - rewrite H10. apply FinalSegment.Charac. split; assumption.
      - intros x H11. rewrite H10 in H11. apply FinalSegment.Charac in H11.
        destruct H11 as [H11 H12]. apply H9; assumption. }
    assert (Minimal R B c) as H12. {
      split.
      - rewrite H10. apply FinalSegment.Charac. split; assumption.
      - intros x H12. rewrite H10 in H12. apply FinalSegment.Charac in H12.
        destruct H12 as [H12 H13]. apply H7; assumption. }
    assert (B :<=: A) as H13. { rewrite H10. apply FinalSegment.IsIncl. }
    assert (Total R A) as H14. { apply H1. }
    assert (c = b) as H15. { apply (Total.MinUnique R A B); assumption. }
    subst. symmetry. apply EqualToClass.
    apply Equiv.Tran with (COS.succ R A a). 1: assumption.
    apply Equiv.Sym, ToClass; assumption.
Qed.

(*
Proposition IsIn : forall (R A:Class) (a:U),
  WellFoundedWellOrd R A  ->
  A a                     ->
  ~ Maximal R A a         ->
  A (succ R A a).
Proof.
  intros R A a H1 H2 H3.
Show.
*)
