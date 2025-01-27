Require Import ZF.Class.
Require Import ZF.Class.Incl.
Require Import ZF.Class.InitSegment.
Require Import ZF.Class.Minimal.
Require Import ZF.Core.And.
Require Import ZF.Core.Equiv.
Require Import ZF.Core.Leq.
Require Import ZF.Core.Zero.
Require Import ZF.Set.
Require Import ZF.Set.Empty.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Singleton.

(* Predicate expressing the fact that R is a founded class on A.                *)
(* R is founded on A iff every non-empty subset of A has an R-minimal element.  *)
(* We wish this predicate to be expressed in the language of set theory, so     *)
(* while Coq allows us to quantify over all subclasses of A, we do not do so.   *)
Definition Founded (R A:Class) : Prop :=
  forall a, toClass a :<=: A /\ a <> :0: -> exists x, Minimal R (toClass a) x.

Proposition FoundedNoLoop1 : forall (R A:Class), Founded R A ->
  forall a, A a -> ~ R :(a,a):.
Proof.
  unfold Founded. intros R A H1 a H2 H3.
  assert (exists x, Minimal R (toClass :{a}:) x) as H4. {
    apply H1. split.
    - apply SingleToClassIncl. assumption.
    - apply SingletonNotEmpty.
  } destruct H4 as [x [H4 H5]].
  apply (InitSegmentEmptyInter1 R (toClass :{a}: ) x a) in H5.
Admitted.
(* toClass :{ a }: :/\: initSegment R x :~: :0: *)

