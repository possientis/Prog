Require Import ZF.Class.Core.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Relation.Bijection.
Require Import ZF.Class.Relation.BijectionOn.
Require Import ZF.Class.Relation.Compose.
Require Import ZF.Class.Relation.Converse.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Fun.
Require Import ZF.Class.Relation.FunctionOn.
Require Import ZF.Class.Relation.Image.
Require Import ZF.Class.Relation.Range.
Require Import ZF.Class.Relation.Restrict.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.OrdPair.

(* F is a bijection from A to B.                                                *)
Definition Bij (F A B:Class) : Prop := BijectionOn F A /\ range F :~: B.

Proposition ImageIsSmall : forall (F A B C:Class),
  Bij F A B -> Small C -> Small F:[C]:.
Proof.
  intros F A B C [H1 _]. apply BijectionOn.ImageIsSmall with A. assumption.
Qed.

Proposition InvImageIsSmall : forall (F A B C:Class),
  Bij F A B -> Small C -> Small F^:-1::[C]:.
Proof.
  intros F A B C [H1 _]. apply BijectionOn.InvImageIsSmall with A. assumption.
Qed.

Proposition IsFun : forall (F A B:Class),
  Bij F A B -> F :: A :-> B.
Proof.
  intros F A B [H1 H2]. apply BijectionOn.IsFunctionOn in H1.
  split. 1: assumption. apply DoubleInclusion, EquivSym. assumption.
Qed.

Proposition ConverseIsBij : forall (F A B:Class),
  Bij F A B -> Bij F^:-1: B A.
Proof.
  intros F A B [[H1 H2] H3]. split.
  - split.
    + apply Bijection.ConverseIsBijection. assumption.
    + apply EquivTran with (range F). 2: assumption. apply ConverseDomain.
  - apply EquivTran with (domain F). 2: assumption. apply ConverseRange.
Qed.

Proposition EvalCharac : forall (F A B:Class) (a y:U),
  Bij F A B -> A a -> F :(a,y): <-> F!a = y.
Proof.
  intros F A B a y H1. apply IsFun in H1.
  apply Fun.EvalCharac with B. assumption.
Qed.

Proposition EvalSatisfies : forall (F A B:Class) (a:U),
  Bij F A B -> A a -> F :(a,F!a):.
Proof.
  intros F A B a H1. apply IsFun in H1.
  apply Fun.EvalSatisfies with B. assumption.
Qed.

Proposition IsInRange : forall (F A B:Class) (x:U),
  Bij F A B -> A x -> B (F!x).
Proof.
  intros F A B a H1. apply IsFun in H1. apply Fun.IsInRange. assumption.
Qed.

Proposition ConverseEvalIsInDomain : forall (F A B:Class) (y:U),
  Bij F A B -> B y -> A (F^:-1:!y).
Proof.
  intros F A B y H1 H2. apply IsInRange with B. 2: assumption.
  apply ConverseIsBij. assumption.
Qed.

Proposition ComposeIsBij : forall (F G A B C:Class),
  Bij F A B -> Bij G B C -> Bij (G :.: F) A C.
Proof.
  intros F G A B C [H1 H2] [H3 H4]. split.
  - apply ComposeIsBijectionOn with B; try assumption.
    apply DoubleInclusion, EquivSym. assumption.
  - apply EquivTran with (range G). 2: assumption.
    apply Compose.RangeIsSame. destruct H3 as [H3 H5].
    apply InclTran with B.
    + apply DoubleInclusion, EquivSym. assumption.
    + apply DoubleInclusion. assumption.
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

Proposition DomainOfComposeCharac : forall (F G A B C:Class) (a:U),
  Bij F A B ->
  Bij G B C ->
  domain (G :.: F) a <-> A a.
Proof.
  intros F G A B C a H1 H2. apply IsFun in H1. apply IsFun in H2.
  apply Fun.DomainOfComposeCharac with B C; assumption.
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

Proposition ImageOfDomainIsRange : forall (F A B:Class),
  Bij F A B -> F:[A]: :~: B.
Proof.
  intros F A B [H1 H2]. apply EquivTran with (range F).
  2: assumption. apply BijectionOn.ImageOfDomainIsRange. assumption.
Qed.

Proposition InvImageOfRangeIsDomain : forall (F A B:Class),
  Bij F A B -> F^:-1::[B]: :~: A.
Proof.
  intros F A B H1. apply ImageOfDomainIsRange, ConverseIsBij. assumption.
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
  apply EquivSym. assumption.
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
