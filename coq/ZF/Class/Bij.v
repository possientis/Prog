Require Import ZF.Class.
Require Import ZF.Class.Bijection.
Require Import ZF.Class.BijectionOn.
Require Import ZF.Class.Compose.
Require Import ZF.Class.Converse.
Require Import ZF.Class.Domain.
Require Import ZF.Class.Fun.
Require Import ZF.Class.FunctionOn.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Range.
Require Import ZF.Class.Restrict.
Require Import ZF.Set.
Require Import ZF.Set.Eval.
Require Import ZF.Set.OrdPair.

(* F is a bijection from A to B.                                                *)
Definition Bij (F A B:Class) : Prop := BijectionOn F A /\ range F :~: B.

Proposition BijIsFun : forall (F A B:Class),
  Bij F A B -> F :: A :-> B.
Proof.
  intros F A B [H1 H2]. apply BijectionOnIsFunctionOn in H1.
  split. 1: assumption. apply DoubleInclusion, ClassEquivSym. assumption.
Qed.

Proposition ConverseIsBij : forall (F A B:Class),
  Bij F A B -> Bij F^:-1: B A.
Proof.
  intros F A B [[H1 H2] H3]. split.
  - split.
    + apply ConverseIsBijection. assumption.
    + apply ClassEquivTran with (range F). 2: assumption. apply ConverseDomain.
  - apply ClassEquivTran with (domain F). 2: assumption. apply ConverseRange.
Qed.

Proposition BijEval : forall (F A B:Class) (a y:U),
  Bij F A B -> A a -> F :(a,y): <-> F!a = y.
Proof.
  intros F A B a y H1. apply BijIsFun in H1.
  apply FunEval with B. assumption.
Qed.

Proposition BijEvalSatisfies : forall (F A B:Class) (a:U),
  Bij F A B -> A a -> F :(a,F!a):.
Proof.
  intros F A B a H1. apply BijIsFun in H1.
  apply FunEvalSatisfies with B. assumption.
Qed.

Proposition BijEvalIsInRange : forall (F A B:Class) (x:U),
  Bij F A B -> A x -> B (F!x).
Proof.
  intros F A B a H1. apply BijIsFun in H1. apply FunEvalIsInRange. assumption.
Qed.

Proposition BijEvalIsInDomain : forall (F A B:Class) (y:U),
  Bij F A B -> B y -> A (F^:-1:!y).
Proof.
  intros F A B y H1 H2. apply BijEvalIsInRange with B. 2: assumption.
  apply ConverseIsBij. assumption.
Qed.

Proposition ComposeIsBij : forall (F G A B C:Class),
  Bij F A B -> Bij G B C -> Bij (G :.: F) A C.
Proof.
  intros F G A B C [H1 H2] [H3 H4]. split.
  - apply ComposeIsBijectionOn with B; try assumption.
    apply DoubleInclusion, ClassEquivSym. assumption.
  - apply ClassEquivTran with (range G). 2: assumption.
    apply ComposeRangeIsSame. destruct H3 as [H3 H5].
    apply InclTran with B.
    + apply DoubleInclusion, ClassEquivSym. assumption.
    + apply DoubleInclusion. assumption.
Qed.

Proposition BijF_FEval : forall (F A B:Class) (x:U),
  Bij F A B -> A x -> F^:-1:!(F!x) = x.
Proof.
  intros F A B x [H1 H2]. apply BijectionOnF_FEval. assumption.
Qed.

Proposition BijFF_Eval : forall (F A B:Class) (y:U),
  Bij F A B -> B y -> F!(F^:-1:!y) = y.
Proof.
  intros F A B y [H1 H2] H3. apply BijectionOnFF_Eval with A. 1: assumption.
  apply H2. assumption.
Qed.

Proposition BijComposeDomainCharac : forall (F G A B C:Class) (a:U),
  Bij F A B ->
  Bij G B C ->
  domain (G :.: F) a <-> A a.
Proof.
  intros F G A B C a H1 H2. apply BijIsFun in H1. apply BijIsFun in H2.
  apply FunComposeDomainCharac with B C; assumption.
Qed.

Proposition BijComposeEval : forall (F G A B C:Class) (a:U),
  Bij F A B ->
  Bij G B C ->
  A a       ->
  (G :.: F)!a = G!(F!a).
Proof.
  intros F G A B C a H1 H2. apply BijIsFun in H1. apply BijIsFun in H2.
  apply FunComposeEval with B C; assumption.
Qed.

