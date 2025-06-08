Require Import ZF.Class.Bounded.
Require Import ZF.Class.Core.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Prod.
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

(* F is an injective function class from A to B.                                *)
Definition Inj (F A B: Class) : Prop := BijectionOn F A /\ range F :<=: B.

(* If F is an injection from A to B, then it is a function from A to B.         *)
Proposition IsFun : forall (F A B:Class), Inj F A B -> F :: A :-> B.
Proof.
  intros F A B [H1 H2]. split. 2: assumption.
  apply BijectionOn.IsFunctionOn. assumption.
Qed.

(* Two injections are equal iff they have same domain and coincide pointwise.   *)
Proposition EquivCharac : forall (F A B G C D:Class),
  Inj F A B ->
  Inj G C D ->
  F :~: G  <->
  A :~: C /\ forall x, A x -> F!x = G!x.
Proof.
  intros F A B G C D H1 H2. apply BijectionOn.EquivCharac.
  - apply H1.
  - apply H2.
Qed.

Proposition ImageOfDomain : forall (F A B:Class),
  Inj F A B -> F:[A]: :~: range F.
Proof.
  intros F A B [H1 _]. apply BijectionOn.ImageOfDomain. assumption.
Qed.

(* An injection F:A -> B is a subclass of AxB.                                  *)
Proposition IsIncl : forall (F A B:Class),
  Inj F A B -> F :<=: A :x: B.
Proof.
  intros F A B H1. apply Fun.IsIncl, IsFun. assumption.
Qed.

(* The image of a small class by an injection from any A to any B is small.     *)
Proposition ImageIsSmall : forall (F A B C:Class),
  Inj F A B -> Small C -> Small F:[C]:.
Proof.
  intros F A B C [H1 _]. apply BijectionOn.ImageIsSmall with A. assumption.
Qed.

(* An injection defined on a small class is small.                              *)
Proposition IsSmall : forall (F A B:Class),
  Inj F A B -> Small A -> Small F.
Proof.
  intros F A B [H1 _]. apply BijectionOn.IsSmall. assumption.
Qed.

(* The inverse image of a small class by an injection from any A to B is small. *)
Proposition InvImageIsSmall : forall (F A B C:Class),
  Inj F A B -> Small C -> Small F^:-1::[C]:.
Proof.
  intros F A B C [H1 _]. apply BijectionOn.InvImageIsSmall with A. assumption.
Qed.

(* If F is an injection fron A to B with range B, F^-1 is an inj from B to A.   *)
Proposition Converse : forall (F A B:Class),
  Inj F A B -> range F :~: B -> Inj F^:-1: B A.
Proof.
  intros F A B [H1 _] H2. split.
  - apply BijectionOn.Converse with A; assumption.
  - apply Incl.EquivCompatL with (domain F).
    + apply EquivSym, ConverseRange.
    + destruct H1 as [_ H1]. apply Incl.EquivCompatR with (domain F). 1: assumption.
      apply InclRefl.
Qed.

(* If F and G are injections then so is the composition G.F.                    *)
Proposition Compose : forall (F G A B C:Class),
  Inj F A B ->
  Inj G B C ->
  Inj (G :.: F) A C.
Proof.
  intros F G A B C [H1 H2] [H3 H4]. split.
  - apply BijectionOn.Compose with B; assumption.
  - apply InclTran with (range G). 2: assumption. apply Compose.RangeIsSmaller.
Qed.

(* An injection from A to B is equal to its restriction to A.                   *)
Proposition IsRestrict : forall (F A B:Class),
  Inj F A B -> F :~: F:|:A.
Proof.
  intros F A B [H1 _]. apply BijectionOn.IsRestrict. assumption.
Qed.

Proposition EvalCharac : forall (F A B:Class) (a y:U),
  Inj F A B -> A a -> F :(a,y): <-> F!a = y.
Proof.
  intros F A B a y [H1 _]. apply BijectionOn.EvalCharac. assumption.
Qed.

Proposition Satisfies : forall (F A B:Class) (a:U),
  Inj F A B -> A a -> F :(a,F!a):.
Proof.
  intros F A B a [H1 _]. apply BijectionOn.Satisfies. assumption.
Qed.

Proposition IsInRange : forall (F A B:Class) (a:U),
  Inj F A B -> A a -> B (F!a).
Proof.
  intros F A B a H1. apply Fun.IsInRange, IsFun. assumption.
Qed.

Proposition ImageCharac : forall (F A B C: Class), Inj F A B ->
  forall y, F:[C]: y <-> exists x, C x /\ A x /\ F!x = y.
Proof.
  intros F A B C H1. apply BijectionOn.ImageCharac, H1.
Qed.

Proposition ConverseEvalIsInDomain : forall (F A B:Class) (b:U),
  Inj F A B -> range F b -> A (F^:-1:!b).
Proof.
  intros F A B b [H1 _]. apply BijectionOn.ConverseEvalIsInDomain. assumption.
Qed.

Proposition ConverseEvalOfEval : forall (F A B:Class) (x:U),
  Inj F A B -> A x -> F^:-1:!(F!x) = x.
Proof.
  intros F A B x [H1 _].
  apply BijectionOn.ConverseEvalOfEval. assumption.
Qed.

Proposition EvalOfConverseEval : forall (F A B:Class) (y:U),
  Inj F A B -> range F y -> F!(F^:-1:!y) = y.
Proof.
  intros F A B y [H1 _].
  apply BijectionOn.EvalOfConverseEval with A. assumption.
Qed.

Proposition DomainOfCompose : forall (F G A B C:Class) (a:U),
  Inj F A B ->
  Inj G B C ->
  domain (G :.: F) a <-> A a.
Proof.
  intros F G A B C a H1 H2. assert (Inj (G :.: F) A C) as H3. {
    apply Compose with B; assumption. }
  destruct H3 as [[_ H3] _]. apply H3.
Qed.

Proposition ComposeEval : forall (F G A B C:Class) (a:U),
  Inj F A B ->
  Inj G B C ->
  A a       ->
  (G :.: F)!a = G!(F!a).
Proof.
  intros F G A B C a [H1 H2] [H3 H4] H5.
  apply BijectionOn.ComposeEval with A B; try assumption.
  apply IsInRange with A. 2: assumption. split; assumption.
Qed.

Proposition InvImageOfRange : forall (F A B:Class),
  Inj F A B -> F^:-1::[range F]: :~: A.
Proof.
  intros F A B [H1 _]. apply BijectionOn.InvImageOfRange. assumption.
Qed.

Proposition RangeIsSmall : forall (F A B:Class),
  Inj F A B -> Small A -> Small (range F).
Proof.
  intros F A B H1. apply BijectionOn.RangeIsSmall, H1.
Qed.

Proposition InvImageOfImage : forall (F A B C:Class),
  Inj F A B -> C :<=: A -> F^:-1::[ F:[C]: ]: :~: C.
Proof.
  intros F A B C [H1 _]. apply BijectionOn.InvImageOfImage. assumption.
Qed.

Proposition ImageOfInvImage : forall (F A B C:Class),
  Inj F A B -> C :<=: range F -> F:[ F^:-1::[C]: ]: :~: C.
Proof.
  intros F A B C [H1 _]. apply BijectionOn.ImageOfInvImage with A. assumption.
Qed.

Proposition EvalInjective : forall (F A B:Class) (x y:U),
  Inj F A B -> A x -> A y -> F!x = F!y -> x = y.
Proof.
  intros F A B x y [H1 _]. apply BijectionOn.EvalInjective. assumption.
Qed.

Proposition EvalInImage : forall (F A B C:Class) (a:U),
  Inj F A B -> A a -> F:[C]: (F!a) <-> C a.
Proof.
  intros F A B C a [H1 _]. apply BijectionOn.EvalInImage. assumption.
Qed.

Proposition RangeIsNotEmpty : forall (F A B:Class),
  Inj F A B -> A :<>: :0: -> range F :<>: :0:.
Proof.
  intros F A B H1. apply BijectionOn.RangeIsNotEmpty, H1.
Qed.
