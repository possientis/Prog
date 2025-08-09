Require Import ZF.Class.Bounded.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Diff.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter2.
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
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.ImageByClass.


(* F is an injective function class from A to B.                                *)
Definition Inj (F A B: Class) : Prop := BijectionOn F A /\ range F :<=: B.

(* If F is an injection from A to B, then it is a function from A to B.         *)
Proposition IsFun : forall (F A B:Class), Inj F A B -> F :: A :-> B.
Proof.
  intros F A B [H1 H2]. split. 2: assumption.
  apply BijectionOn.IsFunctionOn. assumption.
Qed.

(* Two injections are equal iff they have same domain and coincide pointwise.   *)
Proposition EqualCharac : forall (F A B G C D:Class),
  Inj F A B ->
  Inj G C D ->
  F :~: G  <->
  A :~: C /\ forall x, A x -> F!x = G!x.
Proof.
  intros F A B G C D [H1 _] [H2i _]. apply BijectionOn.EqualCharac; assumption.
Qed.

Proposition ImageOfDomain : forall (F A B:Class),
  Inj F A B -> F:[A]: :~: range F.
Proof.
  intros F A B H1. apply BijectionOn.ImageOfDomain, H1.
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

Proposition InvImageOfRange : forall (F A B:Class),
  Inj F A B -> F^:-1::[range F]: :~: A.
Proof.
  intros F A B H1. apply BijectionOn.InvImageOfRange, H1.
Qed.

Proposition RangeIsSmall : forall (F A B:Class),
  Inj F A B -> Small A -> Small (range F).
Proof.
  intros F A B H1. apply BijectionOn.RangeIsSmall, H1.
Qed.

(* If F and G are injections then so is the composition G.F.                    *)
Proposition Compose : forall (F G A B C:Class),
  Inj F A B ->
  Inj G B C ->
  Inj (G :.: F) A C.
Proof.
  intros F G A B C [H1 H2] [H3 H4]. split.
  - apply BijectionOn.Compose with B; assumption.
  - apply Class.Incl.Tran with (range G). 2: assumption.
    apply Compose.RangeIsSmaller.
Qed.

Proposition EvalCharac : forall (F A B:Class) (a y:U),
  Inj F A B -> A a -> F :(a,y): <-> F!a = y.
Proof.
  intros F A B a y H1. apply BijectionOn.EvalCharac, H1.
Qed.

Proposition Satisfies : forall (F A B:Class) (a:U),
  Inj F A B -> A a -> F :(a,F!a):.
Proof.
  intros F A B a H1. apply BijectionOn.Satisfies, H1.
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

Proposition ImageSetCharac : forall (F A B:Class) (a:U), Inj F A B ->
  forall y, y :< F:[a]: <-> exists x, x :< a /\ A x /\ F!x = y.
Proof.
  intros F A B a H1. apply BijectionOn.ImageSetCharac, H1.
Qed.

Proposition DomainOfCompose : forall (F G A B C:Class),
  Inj F A B ->
  Inj G B C ->
  domain (G :.: F) :~: A.
Proof.
  intros F G A B C H1 H2. assert (Inj (G :.: F) A C) as H3. {
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

(* Characterisation of the range of F.                                          *)
Proposition RangeCharac : forall (F A B:Class) (y:U),
  Inj F A B -> range F y <-> exists x, A x /\ F!x = y.
Proof.
  intros F A B y H1. apply BijectionOn.RangeCharac, H1.
Qed.

Proposition RangeIsNotEmpty : forall (F A B:Class),
  Inj F A B -> A :<>: :0: -> range F :<>: :0:.
Proof.
  intros F A B H1. apply BijectionOn.RangeIsNotEmpty, H1.
Qed.

(* An injection from A to B is equal to its restriction to A.                   *)
Proposition IsRestrict : forall (F A B:Class),
  Inj F A B -> F :~: F:|:A.
Proof.
  intros F A B H1. apply BijectionOn.IsRestrict, H1.
Qed.

Proposition Restrict : forall (F A B C:Class),
  Inj F A B -> Inj (F:|:C) (A :/\: C) B.
Proof.
  intros F A B C [H1 H2]. split.
  - apply BijectionOn.Restrict. assumption.
  - apply Class.Incl.Tran with (range F). 2: assumption.
    apply Restrict.RangeIsIncl.
Qed.

Proposition RestrictEqual : forall (F A B G C D E:Class),
  Inj F A B                     ->
  Inj G C D                     ->
  E :<=: A                      ->
  E :<=: C                      ->
  (forall x, E x -> F!x = G!x)  ->
  F:|:E :~: G:|:E.
Proof.
  intros F A B G C D E [H1 H2] [H3 H4].
  apply BijectionOn.RestrictEqual; assumption.
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
    + apply Equiv.Sym, Converse.Range.
    + destruct H1 as [_ H1]. apply Incl.EquivCompatR with (domain F). 1: assumption.
      apply Class.Incl.Refl.
Qed.

Proposition ConverseEvalIsInDomain : forall (F A B:Class) (b:U),
  Inj F A B -> range F b -> A (F^:-1:!b).
Proof.
  intros F A B b H1. apply BijectionOn.ConverseEvalIsInDomain, H1.
Qed.

Proposition ConverseEvalOfEval : forall (F A B:Class) (x:U),
  Inj F A B -> A x -> F^:-1:!(F!x) = x.
Proof.
  intros F A B x H1. apply BijectionOn.ConverseEvalOfEval, H1.
Qed.

Proposition EvalOfConverseEval : forall (F A B:Class) (y:U),
  Inj F A B -> range F y -> F!(F^:-1:!y) = y.
Proof.
  intros F A B y H1. apply BijectionOn.EvalOfConverseEval with A, H1.
Qed.

Proposition InvImageOfImage : forall (F A B C:Class),
  Inj F A B -> C :<=: A -> F^:-1::[ F:[C]: ]: :~: C.
Proof.
  intros F A B C H1. apply BijectionOn.InvImageOfImage, H1.
Qed.

Proposition ImageOfInvImage : forall (F A B C:Class),
  Inj F A B -> C :<=: range F -> F:[ F^:-1::[C]: ]: :~: C.
Proof.
  intros F A B C H1. apply BijectionOn.ImageOfInvImage with A, H1.
Qed.

Proposition EvalInjective : forall (F A B:Class) (x y:U),
  Inj F A B -> A x -> A y -> F!x = F!y -> x = y.
Proof.
  intros F A B x y H1. apply BijectionOn.EvalInjective, H1.
Qed.

Proposition EvalInImage : forall (F A B C:Class) (a:U),
  Inj F A B -> A a -> F:[C]: (F!a) <-> C a.
Proof.
  intros F A B C a H1. apply BijectionOn.EvalInImage, H1.
Qed.

Proposition Inter2Image : forall (F A B C D:Class),
  Inj F A B -> F:[C :/\: D]: :~: F:[C]: :/\: F:[D]:.
Proof.
  intros F A B C D H1. apply BijectionOn.Inter2Image with A, H1.
Qed.

Proposition DiffImage : forall (F A B C D:Class),
  Inj F A B -> F:[C :\: D]: :~: F:[C]: :\: F:[D]:.
Proof.
  intros F A B C D H1. apply BijectionOn.DiffImage with A, H1.
Qed.

