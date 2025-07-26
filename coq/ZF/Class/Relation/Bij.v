Require Import ZF.Class.Equiv.
Require Import ZF.Class.Diff.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.Prod.
Require Import ZF.Class.Relation.Bijection.
Require Import ZF.Class.Relation.BijectionOn.
Require Import ZF.Class.Relation.Compose.
Require Import ZF.Class.Relation.Converse.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Fun.
Require Import ZF.Class.Relation.FunctionOn.
Require Import ZF.Class.Relation.Image.
Require Import ZF.Class.Relation.Inj.
Require Import ZF.Class.Relation.Onto.
Require Import ZF.Class.Relation.Range.
Require Import ZF.Class.Relation.Restrict.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.ImageByClass.


(* F is a bijection from A to B.                                                *)
Definition Bij (F A B:Class) : Prop := BijectionOn F A /\ range F :~: B.

Proposition IsFun : forall (F A B:Class),
  Bij F A B -> F :: A :-> B.
Proof.
  intros F A B [H1 H2]. apply BijectionOn.IsFunctionOn in H1.
  split. 1: assumption. apply DoubleInclusion, Equiv.Sym. assumption.
Qed.

Proposition IsInj : forall (F A B:Class),
  Bij F A B -> Inj F A B.
Proof.
  intros F A B H1. split. 1: apply H1. apply DoubleInclusion, Equiv.Sym, H1.
Qed.

Proposition IsOnto : forall (F A B:Class),
  Bij F A B -> Onto F A B.
Proof.
  intros F A B H1. split. 2: apply H1. apply BijectionOn.IsFunctionOn, H1.
Qed.

(* Two bijections are equal iff they have same domain and coincide pointwise.   *)
Proposition EquivCharac : forall (F A B G C D:Class),
  Bij F A B ->
  Bij G C D ->
  F :~: G  <->
  A :~: C /\ forall x, A x -> F!x = G!x.
Proof.
  intros F A B G C D H1 H2. apply BijectionOn.EquivCharac.
  - apply H1.
  - apply H2.
Qed.

Proposition ImageOfDomain : forall (F A B:Class),
  Bij F A B -> F:[A]: :~: B.
Proof.
  intros F A B [H1 H2]. apply Equiv.Tran with (range F).
  2: assumption. apply BijectionOn.ImageOfDomain. assumption.
Qed.

(* A bijection F:A -> B is a subclass of AxB.                                   *)
Proposition IsIncl : forall (F A B:Class),
  Bij F A B -> F :<=: A :x: B.
Proof.
  intros F A B H1. apply Fun.IsIncl, IsFun. assumption.
Qed.

Proposition ImageIsSmall : forall (F A B C:Class),
  Bij F A B -> Small C -> Small F:[C]:.
Proof.
  intros F A B C [H1 _]. apply BijectionOn.ImageIsSmall with A. assumption.
Qed.

(* A bijection F:A -> B defined on a small class  is small.                     *)
Proposition IsSmall : forall (F A B:Class),
  Bij F A B -> Small A -> Small F.
Proof.
  intros F A B H1. apply BijectionOn.IsSmall, H1.
Qed.

Proposition InvImageOfRange : forall (F A B:Class),
  Bij F A B -> F^:-1::[B]: :~: A.
Proof.
  intros F A B H1. apply Equiv.Tran with F^:-1::[range F]:.
  - apply InvImage.EquivCompatR, Equiv.Sym, H1.
  - apply BijectionOn.InvImageOfRange, H1.
Qed.

Proposition RangeIsSmall : forall (F A B:Class),
  Bij F A B -> Small A -> Small B.
Proof.
  intros F A B H1 H2. apply Small.EquivCompat with (range F).
  - apply H1.
  - apply BijectionOn.RangeIsSmall with A. 2: assumption. apply H1.
Qed.

Proposition Compose : forall (F G A B C:Class),
  Bij F A B -> Bij G B C -> Bij (G :.: F) A C.
Proof.
  intros F G A B C [H1 H2] [H3 H4]. split.
  - apply BijectionOn.Compose with B; try assumption.
    apply DoubleInclusion, Equiv.Sym. assumption.
  - apply Equiv.Tran with (range G). 2: assumption.
    apply Compose.RangeIsSame. destruct H3 as [H3 H5].
    apply Class.Incl.Tran with B.
    + apply DoubleInclusion, Equiv.Sym. assumption.
    + apply DoubleInclusion. assumption.
Qed.

Proposition EvalCharac : forall (F A B:Class) (a y:U),
  Bij F A B -> A a -> F :(a,y): <-> F!a = y.
Proof.
  intros F A B a y H1. apply IsFun in H1.
  apply Fun.EvalCharac with B. assumption.
Qed.

Proposition Satisfies : forall (F A B:Class) (a:U),
  Bij F A B -> A a -> F :(a,F!a):.
Proof.
  intros F A B a H1. apply IsFun in H1.
  apply Fun.Satisfies with B. assumption.
Qed.

Proposition IsInRange : forall (F A B:Class) (x:U),
  Bij F A B -> A x -> B (F!x).
Proof.
  intros F A B a H1. apply IsFun in H1. apply Fun.IsInRange. assumption.
Qed.

Proposition ImageCharac : forall (F A B C: Class), Bij F A B ->
  forall y, F:[C]: y <-> exists x, C x /\ A x /\ F!x = y.
Proof.
  intros F A B C H1. apply BijectionOn.ImageCharac, H1.
Qed.

Proposition ImageSetCharac : forall (F A B:Class) (a:U), Bij F A B ->
  forall y, y :< F:[a]: <-> exists x, x :< a /\ A x /\ F!x = y.
Proof.
  intros F A B a H1. apply BijectionOn.ImageSetCharac, H1.
Qed.

Proposition DomainOfCompose : forall (F G A B C:Class) (a:U),
  Bij F A B ->
  Bij G B C ->
  domain (G :.: F) a <-> A a.
Proof.
  intros F G A B C a H1 H2. apply IsFun in H1. apply IsFun in H2.
  apply Fun.DomainOfCompose with B C; assumption.
Qed.

Proposition ComposeEval : forall (F G A B C:Class) (a:U),
  Bij F A B ->
  Bij G B C ->
  A a       ->
  (G :.: F)!a = G!(F!a).
Proof.
  intros F G A B C a H1 H2. apply IsFun in H1. apply IsFun in H2.
  apply Fun.ComposeEval with B C; assumption.
Qed.

(* Characterisation of the range of F.                                          *)
Proposition RangeCharac : forall (F A B:Class) (y:U),
  Bij F A B -> B y <-> exists x, A x /\ F!x = y.
Proof.
  intros F A B y [H1 H2]. split; intros H3.
  - apply BijectionOn.RangeCharac. 1: assumption. apply H2. assumption.
  - apply H2. apply BijectionOn.RangeCharac with A; assumption.
Qed.

Proposition RangeIsNotEmpty : forall (F A B:Class),
  Bij F A B -> A :<>: :0: -> B :<>: :0:.
Proof.
  intros F A B H1. apply Onto.RangeIsNotEmpty with F, IsOnto. assumption.
Qed.

Proposition IsRestrict : forall (F A B:Class),
  Bij F A B -> F :~: F:|:A.
Proof.
  intros F A B H1. apply BijectionOn.IsRestrict, H1.
Qed.

Proposition InvImageIsSmall : forall (F A B C:Class),
  Bij F A B -> Small C -> Small F^:-1::[C]:.
Proof.
  intros F A B C [H1 _]. apply BijectionOn.InvImageIsSmall with A. assumption.
Qed.

Proposition Converse : forall (F A B:Class),
  Bij F A B -> Bij F^:-1: B A.
Proof.
  intros F A B [[H1 H2] H3]. split.
  - split.
    + apply Bijection.Converse. assumption.
    + apply Equiv.Tran with (range F). 2: assumption. apply Converse.Domain.
  - apply Equiv.Tran with (domain F). 2: assumption. apply Converse.Range.
Qed.

Proposition ConverseEvalIsInDomain : forall (F A B:Class) (y:U),
  Bij F A B -> B y -> A (F^:-1:!y).
Proof.
  intros F A B y H1 H2. apply IsInRange with B. 2: assumption.
  apply Converse. assumption.
Qed.

Proposition ConverseEvalOfEval : forall (F A B:Class) (x:U),
  Bij F A B -> A x -> F^:-1:!(F!x) = x.
Proof.
  intros F A B x [H1 H2]. apply BijectionOn.ConverseEvalOfEval. assumption.
Qed.

Proposition EvalOfConverseEval : forall (F A B:Class) (y:U),
  Bij F A B -> B y -> F!(F^:-1:!y) = y.
Proof.
  intros F A B y [H1 H2] H3.
  apply BijectionOn.EvalOfConverseEval with A. 1: assumption.
  apply H2. assumption.
Qed.

Proposition InvImageOfImage : forall (F A B C:Class),
  Bij F A B -> C :<=: A -> F^:-1::[ F:[C]: ]: :~: C.
Proof.
  intros F A B C [H1 H2] H3. apply BijectionOn.InvImageOfImage with A; assumption.
Qed.

Proposition ImageOfInvImage : forall (F A B C:Class),
  Bij F A B -> C :<=: B -> F:[ F^:-1::[C]: ]: :~: C.
Proof.
  intros F A B C [H1 H2] H3. apply BijectionOn.ImageOfInvImage with A.
  1: assumption. apply Incl.EquivCompatR with B. 2: assumption.
  apply Equiv.Sym. assumption.
Qed.

Proposition EvalInjective : forall (F A B:Class) (x y:U),
  Bij F A B -> A x -> A y -> F!x = F!y -> x = y.
Proof.
  intros F A B x y [H1 _]. apply BijectionOn.EvalInjective. assumption.
Qed.

Proposition EvalInImage : forall (F A B C:Class) (a:U),
  Bij F A B -> A a -> F:[C]: (F!a) <-> C a.
Proof.
  intros F A B C a [H1 _]. apply BijectionOn.EvalInImage. assumption.
Qed.

Proposition Inter2Image : forall (F A B C D:Class),
  Bij F A B -> F:[C :/\: D]: :~: F:[C]: :/\: F:[D]:.
Proof.
  intros F A B C D H1. apply BijectionOn.Inter2Image with A, H1.
Qed.

Proposition DiffImage : forall (F A B C D:Class),
  Bij F A B -> F:[C :\: D]: :~: F:[C]: :\: F:[D]:.
Proof.
  intros F A B C D H1. apply BijectionOn.DiffImage with A, H1.
Qed.
