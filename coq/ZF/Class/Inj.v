Require Import ZF.Class.
Require Import ZF.Class.BijectionOn.
Require Import ZF.Class.Compose.
Require Import ZF.Class.Converse.
Require Import ZF.Class.Domain.
Require Import ZF.Class.Fun.
Require Import ZF.Class.FunctionOn.
Require Import ZF.Class.Image.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Range.
Require Import ZF.Class.Restrict.
Require Import ZF.Class.Small.
Require Import ZF.Set.
Require Import ZF.Set.Eval.
Require Import ZF.Set.OrdPair.

(* F is an injective function class from A to B.                                *)
Definition Inj (F A B: Class) : Prop := BijectionOn F A /\ range F :<=: B.

(* If F is an injection from A to B, then it is a function from A to B.         *)
Proposition InjIsFun : forall (F A B:Class), Inj F A B -> F :: A :-> B.
Proof.
  intros F A B [H1 H2]. split. 2: assumption.
  apply BijectionOnIsFunctionOn. assumption.
Qed.

(* The image of a small class by an injection from any A to any B is small.     *)
Proposition InjImageIsSmall : forall (F A B C:Class),
  Inj F A B -> Small C -> Small F:[C]:.
Proof.
  intros F A B C [H1 _]. apply BijectionOnImageIsSmall with A. assumption.
Qed.

(* The inverse image of a small class by an injection from any A to B is small. *)
Proposition InjInvImageIsSmall : forall (F A B C:Class),
  Inj F A B -> Small C -> Small F^:-1::[C]:.
Proof.
  intros F A B C [H1 _]. apply BijectionOnInvImageIsSmall with A. assumption.
Qed.

(* An injection defined on a small class is small.                              *)
Proposition InjIsSmall : forall (F A B:Class),
  Inj F A B -> Small A -> Small F.
Proof.
  intros F A B [H1 _]. apply BijectionOnIsSmall. assumption.
Qed.

(* If F is an injection fron A to B with range B, F^-1 is an inj from B to A.   *)
Proposition ConverseIsInj : forall (F A B:Class),
  Inj F A B -> range F :~: B -> Inj F^:-1: B A.
Proof.
  intros F A B [H1 _] H2. split.
  - apply ConverseIsBijectionOn with A; assumption.
  - apply InclEquivCompatL with (domain F).
    + apply ClassEquivSym, ConverseRange.
    + destruct H1 as [_ H1]. apply InclEquivCompatR with (domain F). 1: assumption.
      apply InclRefl.
Qed.

(* If F and G are injections then so is the composition G.F.                    *)
Proposition ComposeIsInj : forall (F G A B C:Class),
  Inj F A B ->
  Inj G B C ->
  Inj (G :.: F) A C.
Proof.
  intros F G A B C [H1 H2] [H3 H4]. split.
  - apply ComposeIsBijectionOn with B; assumption.
  - apply InclTran with (range G). 2: assumption. apply ComposeRangeIsSmaller.
Qed.

(* An injection from A to B is equal to its restriction to A.                   *)
Proposition InjIsRestrict : forall (F A B:Class),
  Inj F A B -> F :~: F:|:A.
Proof.
  intros F A B [H1 _]. apply BijectionOnIsRestrict. assumption.
Qed.

Proposition InjEval : forall (F A B:Class) (a y:U),
  Inj F A B -> A a -> F :(a,y): <-> F!a = y.
Proof.
  intros F A B a y [H1 _]. apply BijectionOnEval. assumption.
Qed.

Proposition InjEvalSatisfies : forall (F A B:Class) (a:U),
  Inj F A B -> A a -> F :(a,F!a):.
Proof.
  intros F A B a [H1 _]. apply BijectionOnEvalSatisfies. assumption.
Qed.

Proposition InjEvalIsInRange : forall (F A B:Class) (a:U),
  Inj F A B -> A a -> B (F!a).
Proof.
  intros F A B a H1. apply FunEvalIsInRange, InjIsFun. assumption.
Qed.

Proposition InjEvalIsInDomain : forall (F A B:Class) (b:U),
  Inj F A B -> range F b -> A (F^:-1:!b).
Proof.
  intros F A B b [H1 _]. apply BijectionOnEvalIsInDomain. assumption.
Qed.

Proposition InjF_FEval : forall (F A B:Class) (x:U),
  Inj F A B -> A x -> F^:-1:!(F!x) = x.
Proof.
  intros F A B x [H1 _]. apply BijectionOnF_FEval. assumption.
Qed.

Proposition InjFF_Eval : forall (F A B:Class) (y:U),
  Inj F A B -> range F y -> F!(F^:-1:!y) = y.
Proof.
  intros F A B y [H1 _]. apply BijectionOnFF_Eval with A. assumption.
Qed.

Proposition InjComposeDomainCharac : forall (F G A B C:Class) (a:U),
  Inj F A B ->
  Inj G B C ->
  domain (G :.: F) a <-> A a.
Proof.
  intros F G A B C a H1 H2. assert (Inj (G :.: F) A C) as H3. {
    apply ComposeIsInj with B; assumption. }
  destruct H3 as [[_ H3] _]. apply H3.
Qed.

Proposition InjComposeEval : forall (F G A B C:Class) (a:U),
  Inj F A B ->
  Inj G B C ->
  A a       ->
  (G :.: F)!a = G!(F!a).
Proof.
  intros F G A B C a [H1 H2] [H3 H4] H5.
  apply BijectionOnComposeEval with A B; try assumption.
  apply InjEvalIsInRange with A. 2: assumption. split; assumption.
Qed.

Proposition InjRangeIsDomainImage : forall (F A B:Class),
  Inj F A B -> F:[A]: :~: range F.
Proof.
  intros F A B [H1 _]. apply BijectionOnRangeIsDomainImage. assumption.
Qed.

Proposition InjInvImageOfRangeIsDomain : forall (F A B:Class),
  Inj F A B -> F^:-1::[range F]: :~: A.
Proof.
  intros F A B [H1 _]. apply BijectionOnInvImageOfRangeIsDomain. assumption.
Qed.

Proposition InjInvImageOfImage : forall (F A B C:Class),
  Inj F A B -> C :<=: A -> F^:-1::[ F:[C]: ]: :~: C.
Proof.
  intros F A B C [H1 _]. apply BijectionOnInvImageOfImage. assumption.
Qed.

Proposition InjImageOfInvImage : forall (F A B C:Class),
  Inj F A B -> C :<=: range F -> F:[ F^:-1::[C]: ]: :~: C.
Proof.
  intros F A B C [H1 _]. apply BijectionOnImageOfInvImage with A. assumption.
Qed.

Proposition InjEvalInjective : forall (F A B:Class) (x y:U),
  Inj F A B -> A x -> A y -> F!x = F!y -> x = y.
Proof.
  intros F A B x y [H1 _]. apply BijectionOnEvalInjective. assumption.
Qed.
