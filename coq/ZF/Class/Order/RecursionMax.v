Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Order.Maximal.
Require Import ZF.Class.Order.Recursion.
Require Import ZF.Class.Order.Total.
Require Import ZF.Class.Order.WellFoundedWellOrd.
Require Import ZF.Set.Core.
Require Import ZF.Set.Order.InitSegment.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.RestrictOfClass.
Require Import ZF.Set.Single.
Require Import ZF.Set.Union2.

Module COR := ZF.Class.Order.Recursion.

(* The recursion class associated with R A F. In other words, when R is a well  *)
(* founded well ordering on A and A has a maximal element, the unique function  *)
(* class G defined on A by the recursion G(b) = F(G|initSegment R A b).         *)
Definition Recursion (R A F:Class) : Class := fun x => exists f a,
    Maximal R A a                                                   /\
    f = COR.Recursion R A F :|: initSegment R A a                   /\
    x :< f :\/: :{ :(a,F!f): }:.

Proposition Charac : forall (R A F:Class) (f a x:U),
  WellFoundedWellOrd R A                              ->
  Maximal R A a                                       ->
  f = COR.Recursion R A F :|: initSegment R A a       ->
  Recursion R A F x                                   ->
  x :< f \/ x = :(a,F!f):.
Proof.
  intros R A F f a x H1 H2 H3 H4. destruct H4 as [g [b [H4 [H5 H6]]]].
  assert (a = b) as H7. {
    apply Total.MaxUnique with R A A; try assumption. 1: apply H1.
    apply Class.Incl.Refl. }
  assert (f = g) as H8. { rewrite H7 in H3. rewrite <- H5 in H3. assumption. }
  apply Union2.Charac in H6. destruct H6 as [H6|H6].
  - left. rewrite H8. assumption.
  - right. rewrite H7,H8. apply Single.Charac. assumption.
Qed.

Proposition CharacRev : forall (R A F:Class) (f a x:U),
  WellFoundedWellOrd R A                              ->
  Maximal R A a                                       ->
  f = COR.Recursion R A F :|: initSegment R A a       ->
  x :< f \/ x = :(a,F!f):                             ->
  Recursion R A F x.
Proof.
  intros R A F f a x H1 H2 H3 H4. exists f. exists a.
  split. 1: assumption. split. 1: assumption.
  apply Union2.Charac. destruct H4 as [H4|H4].
  - left. assumption.
  - right. apply Single.Charac. assumption.
Qed.

Proposition Charac2 : forall (R A F:Class) (f a x y:U),
  WellFoundedWellOrd R A                                  ->
  Maximal R A a                                           ->
  f = COR.Recursion R A F :|: initSegment R A a           ->
  Recursion R A F :(x,y):                                 ->
  :(x,y): :< f \/ x = a /\ y = F!f.
Proof.
  intros R A F f a x y H1 H2 H3 H4.
  apply (Charac _ _ _ f a) in H4; try assumption. destruct H4 as [H4|H4].
  - left. assumption.
  - right. apply OrdPair.WhenEqual in H4. destruct H4 as [H4 H5].
    split; assumption.
Qed.

Proposition Charac2Rev : forall (R A F:Class) (f a x y:U),
  WellFoundedWellOrd R A                                  ->
  Maximal R A a                                           ->
  f = COR.Recursion R A F :|: initSegment R A a           ->
  :(x,y): :< f \/ x = a /\ y = F!f                        ->
  Recursion R A F :(x,y):.
Proof.
  intros R A F f a x y H1 H2 H3 H4.
  apply (CharacRev _ _ _ f a); try assumption. destruct H4 as [H4|H4].
  - left. assumption.
  - right. destruct H4 as [H4 H5]. rewrite H4, H5. reflexivity.
Qed.
