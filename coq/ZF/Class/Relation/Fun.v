Require Import ZF.Class.Equiv.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.Prod.
Require Import ZF.Class.Relation.Compose.
Require Import ZF.Class.Relation.Converse.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Class.Relation.Image.
Require Import ZF.Class.Relation.FunctionOn.
Require Import ZF.Class.Relation.Range.
Require Import ZF.Class.Relation.Restrict.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.ImageByClass.

Require Import ZF.Notation.Fun.
Export ZF.Notation.Fun.

(* F is a function from A to B.                                                 *)
Definition Fun (F A B:Class) : Prop := FunctionOn F A /\ range F :<=: B.

(* Notation "F :: A :-> B" := (Fun F A B)                                       *)
Global Instance ClassFun : Notation.Fun.Fun Class Class := { IsFun := Fun }.

(* Two functions are equal iff they have same domain and coincide pointwise.    *)
Proposition EqualCharac : forall (F A B G C D:Class),
  F :: A :-> B  ->
  G :: C :-> D  ->
  F :~: G      <->
  A :~: C /\ forall x, A x -> F!x = G!x.
Proof.
  intros F A B G C D [H1 _] [H2 _]. apply FunctionOn.EqualCharac; assumption.
Qed.

(* The direct image of the domain is the range.                                 *)
Proposition ImageOfDomain : forall (F A B:Class),
  F :: A :-> B -> F:[A]: :~: range F.
Proof.
  intros F A B H1. apply FunctionOn.ImageOfDomain, H1.
Qed.

(* A function F:A -> B is a subclass of AxB.                                    *)
Proposition IsIncl : forall (F A B:Class),
  F :: A :-> B -> F :<=: A :x: B.
Proof.
  intros F A B H1.
  apply Class.Incl.Tran with (A :x: F:[A]:).
  - apply FunctionOn.IsIncl, H1.
  - apply Prod.InclCompatR, Incl.EquivCompatL with (range F).
    2: apply H1. apply Equiv.Sym, ImageOfDomain with B. assumption.
Qed.

(* The direct image of a small class by a function is small.                    *)
Proposition ImageIsSmall : forall (F A B C:Class),
  F :: A :-> B -> Small C -> Small F:[C]:.
Proof.
  intros F A B C H1. apply FunctionOn.ImageIsSmall with A, H1.
Qed.

(* A function defined on a small class is small.                                *)
Proposition IsSmall : forall (F A B:Class),
  F :: A :-> B -> Small A -> Small F.
Proof.
  intros F a B H1. apply FunctionOn.IsSmall, H1.
Qed.

(* The inverse image of the range is the domain.                                *)
Proposition InvImageOfRange : forall (F A B:Class),
  F :: A :-> B -> F^:-1::[range F]: :~: A.
Proof.
  intros F A B H1. apply FunctionOn.InvImageOfRange, H1.
Qed.

(* If F is defined on a small class A, then its range is small.                 *)
Proposition RangeIsSmall : forall (F A B:Class),
  F :: A :-> B -> Small A -> Small (range F).
Proof.
  intros F A B H1. apply FunctionOn.RangeIsSmall, H1.
Qed.

(* If F:A -> B and G:B -> C then G.F : A -> C.                                  *)
Proposition Compose : forall (F G A B C: Class),
  F :: A :-> B          ->
  G :: B :-> C          ->
  (G :.: F) :: A :-> C.
Proof.
  intros F G A B C [H1 H2] [H3 H4]. split.
  - apply FunctionOn.Compose with B; assumption.
  - apply Class.Incl.Tran with (range G). 2: assumption.
    apply Compose.RangeIsSmaller.
Qed.

(* Characterization of the value at a of a function defined on A when a in A.   *)
Proposition EvalCharac : forall (F A B:Class) (a y:U),
  F :: A :-> B -> A a -> F :(a,y): <-> F!a = y.
Proof.
  intros F A B a y H1. apply FunctionOn.EvalCharac, H1.
Qed.

(* The ordered pair (a,F!a) satisfies the predicate F when a in A.              *)
Proposition Satisfies : forall (F A B:Class) (a:U),
  F :: A :-> B -> A a -> F :(a,F!a):.
Proof.
  intros F A B a H1. apply FunctionOn.Satisfies, H1.
Qed.

(* The value at a of a function defined on A lies in B  when a im A.            *)
Proposition IsInRange : forall (F A B:Class) (a:U),
  F :: A :-> B -> A a -> B (F!a).
Proof.
  intros F A B a H1 H2. apply H1.
  apply FunctionOn.IsInRange with A. 2: assumption. apply H1.
Qed.

Proposition ImageCharac : forall (F A B C:Class), F :: A :-> B ->
  forall y, F:[C]: y <-> exists x, C x /\ A x /\ F!x = y.
Proof.
  intros F A B C H1. apply FunctionOn.ImageCharac, H1.
Qed.

Proposition ImageSetCharac : forall (F A B:Class) (a:U), F :: A :-> B ->
  forall y, y :< F:[a]: <-> exists x, x :< a /\ A x /\ F!x = y.
Proof.
  intros F A B a H1. apply FunctionOn.ImageSetCharac, H1.
Qed.

(* Characterization of the domain of G.F.                                       *)
Proposition DomainOfCompose : forall (F G A B C:Class),
  F :: A :-> B  ->
  G :: B :-> C  ->
  domain (G :.: F) :~: A.
Proof.
  intros F G A B C [H1 H2] [H3 H4]. intros a. split; intros H5.
  - apply (FunctionOn.DomainOfCompose F G A B a H1 H3) in H5.
    destruct H5 as [H5 H6]. assumption.
  - apply (FunctionOn.DomainOfCompose F G A B a); try assumption.
    split. 1: assumption.  apply IsInRange with A. 2: assumption.
    split; assumption.
Qed.

(* The value at a of G.F is the value at F!a of G when a in A.                  *)
Proposition ComposeEval : forall (F G A B C:Class) (a:U),
  F :: A :-> B  ->
  G :: B :-> C  ->
  A a           ->
  (G :.: F)!a = G!(F!a).
Proof.
  intros F G A B C a [H1 H2] [H3 H4] H5.
  apply (FunctionOn.ComposeEval F G A B); try assumption.
  apply IsInRange with A. 2: assumption. split; assumption.
Qed.

(* Characterisation of the range of F.                                          *)
Proposition RangeCharac : forall (F A B:Class) (y:U),
  F :: A :-> B -> range F y <-> exists x, A x /\ F!x = y.
Proof.
  intros F A B y H1. apply FunctionOn.RangeCharac, H1.
Qed.

(* If the domain of F is not empty, then neither is the range.                  *)
Proposition RangeIsNotEmpty : forall (F A B:Class),
  F :: A :-> B -> A :<>: :0: -> range F :<>: :0:.
Proof.
  intros F A B H1. apply FunctionOn.RangeIsNotEmpty, H1.
Qed.

Proposition IsRestrict : forall (F A B:Class),
  F :: A :-> B -> F :~: F :|: A.
Proof.
  intros F A B H1. apply FunctionOn.IsRestrict, H1.
Qed.

Proposition Restrict : forall (F A B C:Class),
  F :: A :-> B -> (F:|:C) :: (A :/\: C) :-> B.
Proof.
  intros F A B C H1. split.
  - apply FunctionOn.Restrict, H1.
  - apply Class.Incl.Tran with (range F).
    + apply Restrict.RangeIsIncl.
    + apply H1.
Qed.

Proposition RestrictEqual : forall (F A B G C D E:Class),
  F :: A :-> B                  ->
  G :: C :-> D                  ->
  E :<=: A                      ->
  E :<=: C                      ->
  (forall x, E x -> F!x = G!x)  ->
  F:|:E :~: G:|:E.
Proof.
  intros F A B G C D E [H1 H2] [H3 H4].
  apply FunctionOn.RestrictEqual; assumption.
Qed.

