Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Relation.Bij.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Relation.Image.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.Order.InitSegment.
Require Import ZF.Class.Order.Isom.
Require Import ZF.Set.Core.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.OrdPair.

(* Predicate expressing the fact that a is an R-minimal element of A.           *)
Definition Minimal (R A:Class) (a:U) : Prop
  := A a /\ initSegment R A a :~: :0:.

Proposition Charac : forall (R A:Class) (a:U),
  Minimal R A a <-> A a /\ (forall x, A x -> ~ R :(x,a):).
Proof.
  intros R A a. split; intros [H1 H2].
  - split. 1: assumption. intros x. apply InitSegment.WhenEmpty. assumption.
  - split. 1: assumption. apply InitSegment.WhenEmptyRev. assumption.
Qed.

Proposition EquivCompat : forall (R S A B:Class) (a:U),
  R :~: S -> A :~: B -> Minimal R A a -> Minimal S B a.
Proof.
  intros R S A B a H1 H2 [H3 H4]; split.
  - apply H2. assumption.
  - apply Equiv.Tran with (initSegment R A a). 2: assumption.
    apply Equiv.Sym, InitSegment.EquivCompat; assumption.
Qed.

Proposition EquivCompatL : forall (R S A:Class) (a:U),
  R :~: S -> Minimal R A a -> Minimal S A a.
Proof.
  intros R S A a H1. apply EquivCompat.
  - assumption.
  - apply Equiv.Refl.
Qed.

Proposition EquivCompatR : forall (R A B:Class) (a:U),
  A :~: B -> Minimal R A a -> Minimal R B a.
Proof.
  intros R A B a H1. apply EquivCompat.
  - apply Equiv.Refl.
  - assumption.
Qed.

Proposition IsIn : forall (R A:Class) (a:U),
  Minimal R A a -> A a.
Proof.
  intros R A a H1. apply Charac in H1. apply H1.
Qed.

Proposition NotLess : forall (R A:Class) (a x:U),
  A x -> Minimal R A a -> ~ R :(x,a):.
Proof.
  intros R A a x H1 H2. apply Charac in H2. destruct H2 as [_ H2].
  apply H2; assumption.
Qed.

Proposition IsomImage : forall (F R S A B C:Class) (a:U),
  Isom F R S A B          ->
  C :<=: A                ->
  A a                     ->
  Minimal R C a           ->
  Minimal S F:[C]: (F!a).
Proof.
  intros F R S A B C a H1 H2 H3 [H4 H5]. split.
  - exists a. split. 1: assumption. apply Bij.Satisfies with A B.
    2: assumption. apply H1.
  - apply InitSegment.IsomWhenEmpty with R A B; assumption.
Qed.

Proposition HasNone : forall (R A:Class) (a:U),
  A a                        ->
  ~(exists a, Minimal R A a) ->
   exists b, A b /\ R :(b,a):.
Proof.
  intros R A a H1 H2. apply DoubleNegation. intros H3.
  apply H2. exists a. apply Charac. split. 1: assumption.
  intros b H4 H5. apply H3. exists b. split; assumption.
Qed.
