Require Import ZF.Class.Equiv.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Prod.
Require Import ZF.Class.Relation.Compose.
Require Import ZF.Class.Relation.Converse.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Fun.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Class.Relation.FunctionOn.
Require Import ZF.Class.Relation.Image.
Require Import ZF.Class.Relation.InvImage.
Require Import ZF.Class.Relation.Range.
Require Import ZF.Class.Relation.Restrict.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.ImageByClass.


(* F is a surjective function class from A to B.                                *)
Definition Onto (F A B:Class) : Prop := FunctionOn F A /\ range F :~: B.

Proposition IsFun : forall (F A B:Class), Onto F A B -> Fun F A B.
Proof.
  intros F A B H1. split. 1: apply H1. apply DoubleInclusion, Equiv.Sym, H1.
Qed.

(* Two surjections are equal iff they have same domain and coincide pointwise.  *)
Proposition EqualCharac : forall (F A B G C D:Class),
  Onto F A B ->
  Onto G C D ->
  F :~: G   <->
  A :~: C /\ forall x, A x -> F!x = G!x.
Proof.
  intros F A B G C D H1 H2. apply FunctionOn.EqualCharac.
  - apply H1.
  - apply H2.
Qed.

(* The direct image of the domain is the range.                                 *)
Proposition ImageOfDomain : forall (F A B:Class),
  Onto F A B -> F:[A]: :~: B.
Proof.
  intros F A B H1. apply Equiv.Tran with (range F).
  - apply FunctionOn.ImageOfDomain, H1.
  - apply H1.
Qed.

(* A surjection F:A -> B is a subclass of AxB.                                  *)
Proposition IsIncl : forall (F A B:Class),
  Onto F A B -> F :<=: A :x: B.
Proof.
  intros F A B H1. apply Fun.IsIncl, IsFun. assumption.
Qed.

(* The direct image of a small class by a surjection F:A -> B is small.         *)
Proposition ImageIsSmall : forall (F A B C:Class),
  Onto F A B -> Small C -> Small F:[C]:.
Proof.
  intros F A B C H1. apply FunctionOn.ImageIsSmall with A, H1.
Qed.

(* A surjection F:A -> B defined on a small class is small.                     *)
Proposition IsSmall : forall (F A B:Class),
  Onto F A B -> Small A -> Small F.
Proof.
  intros F A B H1. apply FunctionOn.IsSmall, H1.
Qed.

(* The inverse image of the range is the domain.                                *)
Proposition InvImageOfRange : forall (F A B:Class),
  Onto F A B -> F^:-1::[B]: :~: A.
Proof.
  intros F A B H1. apply Equiv.Tran with F^:-1::[range F]:.
  - apply InvImage.EquivCompat. 1: apply Equiv.Refl. apply Equiv.Sym, H1.
  - apply FunctionOn.InvImageOfRange, H1.
Qed.

(* If F is defined on a small class A, then its range is small.                 *)
Proposition RangeIsSmall : forall (F A B:Class),
  Onto F A B -> Small A -> Small B.
Proof.
  intros F A B H1 H2. apply Small.EquivCompat with (range F).
  - apply H1.
  - apply FunctionOn.RangeIsSmall with A. 2: assumption. apply H1.
Qed.

(* If F and G are surjections then so is the composition G.F.                   *)
Proposition Compose : forall (F G A B C:Class),
  Onto F A B ->
  Onto G B C ->
  Onto (G :.: F) A C.
Proof.
  intros F G A B C [H1 H2] [H3 H4]. split.
  - apply FunctionOn.Compose with B; try assumption.
    apply Incl.EquivCompatL with B. 2: apply Class.Incl.Refl.
    apply Equiv.Sym. assumption.
  - apply Equiv.Tran with (range G). 2: assumption.
    apply Compose.RangeIsSame, DoubleInclusion, Equiv.Tran with B. 1: assumption.
    apply Equiv.Sym, H3.
Qed.

Proposition EvalCharac : forall (F A B:Class) (a y:U),
  Onto F A B -> A a -> F :(a,y): <-> F!a = y.
Proof.
  intros F A B a y H1. apply FunctionOn.EvalCharac, H1.
Qed.

Proposition Satisfies : forall (F A B:Class) (a:U),
  Onto F A B -> A a -> F :(a,F!a):.
Proof.
  intros F A B a H1. apply FunctionOn.Satisfies, H1.
Qed.

Proposition IsInRange : forall (F A B:Class) (a:U),
  Onto F A B -> A a -> B (F!a).
Proof.
  intros F A B a H1 H2. apply H1.
  apply FunctionOn.IsInRange with A. 2: assumption. apply H1.
Qed.

Proposition ImageCharac : forall (F A B C: Class), Onto F A B ->
  forall y, F:[C]: y <-> exists x, C x /\ A x /\ F!x = y.
Proof.
  intros F A B C H1. apply FunctionOn.ImageCharac, H1.
Qed.

Proposition ImageSetCharac : forall (F A B:Class) (a:U), Onto F A B ->
  forall y, y :< F:[a]: <-> exists x, x :< a /\ A x /\ F!x = y.
Proof.
  intros F A B a H1. apply FunctionOn.ImageSetCharac, H1.
Qed.

Proposition DomainOfCompose : forall (F G A B C:Class),
  Onto F A B  ->
  Onto G B C  ->
  domain (G :.: F) :~: A.
Proof.
  intros F G A B C [H1 H2] [H3 H4]. intros a. split; intros H5.
  - apply (FunctionOn.DomainOfCompose F G A B a H1 H3) in H5.
    destruct H5 as [H5 H6]. assumption.
  - apply (FunctionOn.DomainOfCompose F G A B a); try assumption.
    split. 1: assumption.  apply IsInRange with A.
    + split; assumption.
    + assumption.
Qed.

(* The value at a of G.F is the value at F!a of G when a in A.                  *)
Proposition ComposeEval : forall (F G A B C:Class) (a:U),
  Onto F A B ->
  Onto G B C ->
  A a           ->
  (G :.: F)!a = G!(F!a).
Proof.
  intros F G A B C a [H1 H2] [H3 H4] H5.
  apply (FunctionOn.ComposeEval F G A B); try assumption.
  apply IsInRange with A.
  - split; assumption.
  - assumption.
Qed.

(* Characterisation of the range of F.                                          *)
Proposition RangeCharac : forall (F A B:Class) (y:U),
  Onto F A B -> B y <-> exists x, A x /\ F!x = y.
Proof.
  intros F A B y [H1 H2]. split; intros H3.
  - apply FunctionOn.RangeCharac. 1: assumption. apply H2. assumption.
  - apply H2. apply FunctionOn.RangeCharac with A; assumption.
Qed.

(* If the domain of F is not empty, then neither is the range.                  *)
Proposition RangeIsNotEmpty : forall (F A B:Class),
  Onto F A B -> A :<>: :0: -> B :<>: :0:.
Proof.
  intros F A B H1 H2 H3.
  assert (range F :~: :0:) as H4. {
    apply Equiv.Tran with B. 2: assumption. apply H1. }
  revert H4. replace (range F :~: :0: -> False) with (range F :<>: :0:).
  2: reflexivity. apply FunctionOn.RangeIsNotEmpty with A.
  2: assumption. apply H1.
Qed.

Proposition IsRestrict : forall (F A B:Class),
  Onto F A B -> F :~: F :|: A.
Proof.
  intros F A B H1. apply FunctionOn.IsRestrict, H1.
Qed.

