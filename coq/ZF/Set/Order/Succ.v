Require Import ZF.Class.Equiv.
Require Import ZF.Class.Order.Maximal.
Require Import ZF.Class.Order.Succ.
Require Import ZF.Class.Order.WellFoundedWellOrd.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Truncate.

Module COS := ZF.Class.Order.Succ.

Definition succ (R A:Class) (a:U) : U := truncate (COS.succ R A a).

Proposition ToClass : forall (R A:Class) (a:U),
  WellFoundedWellOrd R A                    ->
  A a                                       ->
  toClass (succ R A a) :~: COS.succ R A a.
Proof.
  intros R A a H1 H2.
  apply Truncate.WhenSmall, COS.IsSmall; assumption.
Qed.

Proposition Charac : forall (R A:Class) (a x:U),
  WellFoundedWellOrd R A                        ->
  A a                                           ->
  succ R A a = x                               <->
  A x                                           /\
  R :(a,x):                                     /\
  forall y, A y -> R :(a,y): -> ~ R :(y,x):.
Proof.
  intros R A a x H1 H2. split; intros H3.
  -
Admitted.

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
