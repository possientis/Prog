Require Import ZF.Class.Equiv.
Require Import ZF.Class.Diff.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.Relation.Bijection.
Require Import ZF.Class.Relation.BijectionOn.
Require Import ZF.Class.Relation.Compose.
Require Import ZF.Class.Relation.Converse.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Fun.
Require Import ZF.Class.Relation.FunctionOn.
Require Import ZF.Class.Relation.Image.
Require Import ZF.Class.Relation.Inj.
Require Import ZF.Class.Relation.OneToOne.
Require Import ZF.Class.Relation.Onto.
Require Import ZF.Class.Relation.Range.
Require Import ZF.Class.Relation.Restrict.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.ImageUnderClass.


Module CIN := ZF.Class.Incl.

(* F is a bijection class from A to B.                                          *)
Definition Bij (F A B:Class) : Prop := BijectionOn F A /\ range F :~: B.

(* Bij is compatible with class equivalence in all three arguments.             *)
Proposition EquivCompat : forall (F G A B C D:Class),
  F :~: G   ->
  A :~: C   ->
  B :~: D   ->
  Bij F A B ->
  Bij G C D.
Proof.
  intros F G A B C D H1 H2 H3 [H4 H5]. split.
  - apply BijectionOn.EquivCompat with F A; assumption.
  - apply Equiv.EquivCompat with (range F) B; try assumption.
    apply Range.EquivCompat. assumption.
Qed.

(* Bij is compatible with class equivalence in the first argument.              *)
Proposition EquivCompatL : forall (F G A B:Class),
  F :~: G -> Bij F A B -> Bij G A B.
Proof.
  intros F G A B H1. apply EquivCompat. 1: assumption.
  - apply Equiv.Refl.
  - apply Equiv.Refl.
Qed.

(* Bij is compatible with class equivalence in the second argument.             *)
Proposition EquivCompatM : forall (F A B C:Class),
  A :~: C -> Bij F A B -> Bij F C B.
Proof.
  intros F A B C H1. apply EquivCompat. 2: assumption.
  - apply Equiv.Refl.
  - apply Equiv.Refl.
Qed.

(* Bij is compatible with class equivalence in the third argument.              *)
Proposition EquivCompatR : forall (F A B C:Class),
  B :~: C -> Bij F A B -> Bij F A C.
Proof.
  intros F A B C H1. apply EquivCompat. 3: assumption.
  - apply Equiv.Refl.
  - apply Equiv.Refl.
Qed.

(* A bijection from A to B is a function from A to B.                           *)
Proposition IsFun : forall (F A B:Class),
  Bij F A B -> Fun F A B.
Proof.
  intros F A B [H1 H2]. apply BijectionOn.IsFunctionOn in H1.
  split. 1: assumption. apply CIN.Double, Equiv.Sym. assumption.
Qed.

(* A bijection from A to B is one-to-one as a class relation.                   *)
Proposition IsOneToOne : forall (F A B:Class),
  Bij F A B -> OneToOne F.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros F A B [[[H1 H2] H3] H4]. assumption.
Qed.

(* A bijection from A to B is a function defined on A.                          *)
Proposition IsFunctionOn : forall (F A B:Class),
  Bij F A B -> FunctionOn F A.
Proof.
  intros F A B H1. apply IsFun in H1. apply H1.
Qed.

(* A bijection from A to B is an injection from A to B.                         *)
Proposition IsInj : forall (F A B:Class),
  Bij F A B -> Inj F A B.
Proof.
  intros F A B H1. split. 1: apply H1. apply CIN.Double, Equiv.Sym, H1.
Qed.

(* A bijection from A to B is a surjection from A to B.                         *)
Proposition IsOnto : forall (F A B:Class),
  Bij F A B -> Onto F A B.
Proof.
  intros F A B H1. split. 2: apply H1. apply BijectionOn.IsFunctionOn, H1.
Qed.

(* Two bijections are equal iff they have same domain and coincide pointwise.   *)
Proposition Equal' : forall (F A B G C D:Class),
  Bij F A B ->
  Bij G C D ->
  F :~: G  <->
  A :~: C /\ forall x, A x -> F!x = G!x.
Proof.
  intros F A B G C D [H1 _] [H2i _]. apply BijectionOn.Equal'; assumption.
Qed.

(* Two bijections from A to B that agree pointwise on A are equal.              *)
Proposition Equal : forall (F G A B:Class),
  Bij F A B                     ->
  Bij G A B                     ->
  (forall x, A x -> F!x = G!x)  ->
  F :~: G.
Proof.
  intros F G A B H1 H2 H3.
  apply (Equal' F A B G A B H1 H2). split. 2: assumption. apply Equiv.Refl.
Qed.

(* The image of A under a bijection from A to B is equal to B.                  *)
Proposition ImageOfDomain : forall (F A B:Class),
  Bij F A B -> F:[A]: :~: B.
Proof.
  intros F A B [H1 H2]. apply Equiv.Tran with (range F).
  2: assumption. apply BijectionOn.ImageOfDomain. assumption.
Qed.


(* The image of a small class under a bijection from A to B is small.           *)
Proposition ImageIsSmall : forall (F A B C:Class),
  Bij F A B -> Small C -> Small F:[C]:.
Proof.
  intros F A B C [H1 _]. apply BijectionOn.ImageIsSmall with A. assumption.
Qed.

(* A bijection F:A -> B defined on a small class is small.                      *)
Proposition IsSmall : forall (F A B:Class),
  Bij F A B -> Small A -> Small F.
Proof.
  intros F A B H1. apply BijectionOn.IsSmall, H1.
Qed.

(* The inverse image of B under a bijection from A to B is equal to A.          *)
Proposition InvImageOfRange : forall (F A B:Class),
  Bij F A B -> F^:-1::[B]: :~: A.
Proof.
  intros F A B H1. apply Equiv.Tran with F^:-1::[range F]:.
  - apply InvImage.EquivCompatR, Equiv.Sym, H1.
  - apply BijectionOn.InvImageOfRange, H1.
Qed.

(* If a bijection from A to B has a small domain A, then B is small.            *)
Proposition RangeIsSmall : forall (F A B:Class),
  Bij F A B -> Small A -> Small B.
Proof.
  intros F A B H1 H2. apply Small.EquivCompat with (range F).
  - apply H1.
  - apply BijectionOn.RangeIsSmall with A. 2: assumption. apply H1.
Qed.

(* If a bijection from A to B has a small codomain B, then A is small.          *)
Proposition DomainIsSmall : forall (F A B:Class),
  Bij F A B -> Small B -> Small A.
Proof.
  intros F A B H1. apply Fun.DomainIsSmall with F.
  - apply IsFun. assumption.
  - apply H1.
Qed.

(* The composition of two bijections is a bijection.                            *)
Proposition Compose : forall (F G A B C:Class),
  Bij F A B -> Bij G B C -> Bij (G :.: F) A C.
Proof.
  intros F G A B C [H1 H2] [H3 H4]. split.
  - apply BijectionOn.Compose with B; try assumption.
    apply CIN.Double, Equiv.Sym. assumption.
  - apply Equiv.Tran with (range G). 2: assumption.
    apply Compose.RangeIsSame. destruct H3 as [H3 H5].
    apply CIN.Tran with B.
    + apply CIN.Double, Equiv.Sym. assumption.
    + apply CIN.Double. assumption.
Qed.

Proposition Eval' : forall (F A B:Class) (a y:U),
  Bij F A B -> A a -> F :(a,y): <-> F!a = y.
Proof.
  intros F A B a y H1. apply IsFun in H1. apply Fun.Eval' with B. assumption.
Qed.

Proposition Eval : forall (F A B:Class) (a y:U),
  Bij F A B -> F :(a,y): -> F!a = y.
Proof.
  intros F A B a y H1 H2. apply Eval' with A B; try assumption.
  apply H1. exists y. assumption.
Qed.

Proposition Satisfies : forall (F A B:Class) (a:U),
  Bij F A B -> A a -> F :(a,F!a):.
Proof.
  intros F A B a H1. apply IsFun in H1. apply Fun.Satisfies with B. assumption.
Qed.

(* If a lies in A, the value F!a lies in B for a bijection from A to B.         *)
Proposition IsInRange : forall (F A B:Class) (x:U),
  Bij F A B -> A x -> B F!x.
Proof.
  intros F A B a H1. apply IsFun in H1. apply Fun.IsInRange. assumption.
Qed.

Proposition ImageCharac : forall (F A B C:Class), Bij F A B ->
  forall y, F:[C]: y <-> exists x, C x /\ A x /\ F!x = y.
Proof.
  intros F A B C H1. apply BijectionOn.ImageCharac, H1.
Qed.

Proposition ImageSetCharac : forall (F A B:Class) (a:U), Bij F A B ->
  forall y, y :< F:[a]: <-> exists x, x :< a /\ A x /\ F!x = y.
Proof.
  intros F A B a H1. apply BijectionOn.ImageSetCharac, H1.
Qed.

(* The domain of the composition of two bijections equals the first domain.     *)
Proposition DomainOfCompose : forall (F G A B C:Class),
  Bij F A B               ->
  Bij G B C               ->
  domain (G :.: F) :~: A.
Proof.
  intros F G A B C H1 H2. apply IsFun in H1. apply IsFun in H2.
  apply Fun.DomainOfCompose with B C; assumption.
Qed.

(* The value at a of the composition G.F equals the value at F!a of G.          *)
Proposition ComposeEval : forall (F G A B C:Class) (a:U),
  Bij F A B               ->
  Bij G B C               ->
  A a                     ->
  (G :.: F)!a = G!(F!a).
Proof.
  intros F G A B C a H1 H2.
  apply Fun.ComposeEval with B C; apply IsFun; assumption.
Qed.

Proposition RangeCharac : forall (F A B:Class) (y:U),
  Bij F A B -> B y <-> exists x, A x /\ F!x = y.
Proof.
  intros F A B y [H1 H2]. split; intros H3.
  - apply BijectionOn.RangeCharac. 1: assumption. apply H2. assumption.
  - apply H2. apply BijectionOn.RangeCharac with A; assumption.
Qed.

(* The image of a subclass of A under a bijection from A to B is a subset of B. *)
Proposition ImageIncl : forall (F A B C:Class),
  Bij F A B -> C :<=: A -> F:[C]: :<=: B.
Proof.
  intros F A B C H1 H2 y H3.
  destruct H3 as [x [H3 H4]]. apply H1. exists x. assumption.
Qed.

(* If the domain of a bijection from A to B is non-empty, then B is non-empty.  *)
Proposition RangeIsNotEmpty : forall (F A B:Class),
  Bij F A B -> A :<>: :0: -> B :<>: :0:.
Proof.
  intros F A B H1. apply Onto.RangeIsNotEmpty with F, IsOnto. assumption.
Qed.

(* A bijection from A to B equals its own restriction to A.                     *)
Proposition IsRestrict : forall (F A B:Class),
  Bij F A B -> F :~: F:|:A.
Proof.
  intros F A B H1. apply BijectionOn.IsRestrict, H1.
Qed.

(* The restriction of a bijection from A to B to a subclass C of A is a bij.    *)
Proposition Restrict : forall (F A B C:Class),
  Bij F A B ->  C :<=: A -> Bij (F:|:C) C F:[C]:.
Proof.
  intros F A B C [H1 H2] H3. split.
  - apply BijectionOn.Restrict with A; assumption.
  - apply Restrict.RangeOf.
Qed.

(* Two bijections that agree pointwise on E have equal restrictions to E.       *)
Proposition RestrictEqual : forall (F A B G C D E:Class),
  Bij F A B                     ->
  Bij G C D                     ->
  E :<=: A                      ->
  E :<=: C                      ->
  (forall x, E x -> F!x = G!x)  ->
  F:|:E :~: G:|:E.
Proof.
  intros F A B G C D E [H1 _] [H2 _]. apply BijectionOn.RestrictEqual; assumption.
Qed.

(* The inverse image of a small class under a bijection is small.               *)
Proposition InvImageIsSmall : forall (F A B C:Class),
  Bij F A B -> Small C -> Small F^:-1::[C]:.
Proof.
  intros F A B C [H1 _]. apply BijectionOn.InvImageIsSmall with A. assumption.
Qed.

(* The converse of a bijection from A to B is a bijection from B to A.          *)
Proposition Converse : forall (F A B:Class),
  Bij F A B -> Bij F^:-1: B A.
Proof.
  intros F A B [H1 H2]. split.
  - apply BijectionOn.Converse with A; assumption.
  - destruct H1 as [_ H1]. apply Equiv.Tran with (domain F). 2: assumption.
    apply Converse.Range.
Qed.

(* If y lies in B, the value of the converse at y lies in A.                    *)
Proposition ConverseEvalIsInDomain : forall (F A B:Class) (y:U),
  Bij F A B -> B y -> A (F^:-1:!y).
Proof.
  intros F A B y H1 H2. apply IsInRange with B. 2: assumption.
  apply Converse. assumption.
Qed.

(* Applying the converse after F recovers the original element of A.            *)
Proposition ConverseEvalOfEval : forall (F A B:Class) (x:U),
  Bij F A B -> A x -> F^:-1:!(F!x) = x.
Proof.
  intros F A B x H1. apply BijectionOn.ConverseEvalOfEval, H1.
Qed.

(* Applying F after the converse recovers the original element of B.            *)
Proposition EvalOfConverseEval : forall (F A B:Class) (y:U),
  Bij F A B -> B y -> F!(F^:-1:!y) = y.
Proof.
  intros F A B y [H1 H2] H3.
  apply BijectionOn.EvalOfConverseEval with A. 1: assumption.
  apply H2. assumption.
Qed.

(* The inverse image of the image of C under a bijection from A to B equals C.  *)
Proposition InvImageOfImage : forall (F A B C:Class),
  Bij F A B -> C :<=: A -> F^:-1::[ F:[C]: ]: :~: C.
Proof.
  intros F A B C [H1 H2] H3. apply BijectionOn.InvImageOfImage with A; assumption.
Qed.

(* The image of the inverse image of C under a bijection from A to B equals C.  *)
Proposition ImageOfInvImage : forall (F A B C:Class),
  Bij F A B -> C :<=: B -> F:[ F^:-1::[C]: ]: :~: C.
Proof.
  intros F A B C [H1 H2] H3. apply BijectionOn.ImageOfInvImage with A.
  1: assumption. apply Incl.EquivCompatR with B. 2: assumption.
  apply Equiv.Sym. assumption.
Qed.

(* A bijection from A to B is injective: equal values imply equal arguments.    *)
Proposition EvalInjective : forall (F A B:Class) (x y:U),
  Bij F A B -> A x -> A y -> F!x = F!y -> x = y.
Proof.
  intros F A B x y H1. apply BijectionOn.EvalInjective, H1.
Qed.

(* The value F!a lies in the image of C iff a lies in C, for a bijection.       *)
Proposition EvalInImage : forall (F A B C:Class) (a:U),
  Bij F A B -> A a -> F:[C]: F!a <-> C a.
Proof.
  intros F A B C a H1. apply BijectionOn.EvalInImage, H1.
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

