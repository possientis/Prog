Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Order.InitSegment.
Require Import ZF.Class.Order.Isom.
Require Import ZF.Class.Order.Total.
Require Import ZF.Class.Relation.Bij.
Require Import ZF.Class.Relation.Image.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.EvalOfClass.

(* Predicate expressing the fact that a is an R-minimal element of A.           *)
Definition Minimal (R A:Class) (a:U) : Prop
  := A a /\ (forall x, A x -> ~ R :(x,a):).

Definition HasMinimal R A : Prop := exists a, Minimal R A a.

Definition HasNoMinimal R A : Prop := ~ HasMinimal R A.

Proposition EquivCompat : forall (R S A B:Class) (a:U),
  R :~: S -> A :~: B -> Minimal R A a -> Minimal S B a.
Proof.
  intros R S A B a H1 H2 [H3 H4]; split.
  - apply H2. assumption.
  - intros x H5 H6. apply H4 with x.
    + apply H2. assumption.
    + apply H1. assumption.
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
  intros R A a H1. apply H1.
Qed.

Proposition WhenIn : forall (R A B:Class) (a b:U),
  Total R A             ->
  B :<=: A              ->
  Minimal R B a         ->
  B b                   ->
  a = b \/ R :(a,b):.
Proof.
  intros R A B a b H1 H2 H3 H4.
  assert (a = b \/ R :(a,b): \/ R :(b,a):) as H5. {
    apply H1; apply H2. 2: assumption. apply IsIn with R. assumption. }
  destruct H5 as [H5|[H5|H5]].
  - left. assumption.
  - right. assumption.
  - exfalso. revert H5. apply H3. assumption.
Qed.

Proposition WhenHasNone : forall (R A:Class) (a:U),
  A a                           ->
  HasNoMinimal R A              ->
   exists b, A b /\ R :(b,a):.
Proof.
  intros R A a H1 H2. apply DoubleNegation. intros H3.
  apply H2. exists a. split. 1: assumption.
  intros b H4 H5. apply H3. exists b. split; assumption.
Qed.

Proposition IsomImage : forall (F R S A B C:Class) (a:U),
  Isom F R S A B          ->
  C :<=: A                ->
  A a                     ->
  Minimal R C a           ->
  Minimal S F:[C]: (F!a).
Proof.
  intros F R S A B C a H1 H2 H3 [H4 H5]. split.
  - apply (Bij.ImageCharac F A B). 1: apply H1.
    exists a. split. 1: assumption. split. 1: assumption. reflexivity.
  - intros y H6 H7. apply (Bij.ImageCharac F A B C) in H6. 2: apply H1.
    destruct H6 as [x [H6 [H8 H9]]]. rewrite <- H9 in H7.
    apply H1 in H7; try assumption. specialize (H5 x H6). contradiction.
Qed.

Proposition EmptySegment : forall (R A:Class) (a:U),
  Minimal R A a <-> A a /\ initSegment R A a :~: :0:.
Proof.
  intros R A a. split; intros [H1 H2].
  - split. 1: assumption. apply InitSegment.WhenEmptyRev. assumption.
  - split. 1: assumption. intros x. apply InitSegment.WhenEmpty. assumption.
Qed.

(* If R is total on A the minimal element of a subclass of A is unique.         *)
Proposition Unique : forall (R A B:Class) (x y:U),
  Total R A       ->
  B :<=: A        ->
  Minimal R B x   ->
  Minimal R B y   ->
  x = y.
Proof.

  (* Let R A B be arbitrary classes and x y arbitrary sets. *)
  intros R A B x y.

  (* We assume that R is a total on A. *)
  intros H1. assert (Total R A) as X. apply H1. clear X.

  (* We assume that B is a subclass of A. *)
  intros H2. assert (B :<=: A) as X. apply H2. clear X.

  (* We assume that x is R-minimal in B. *)
  intros H3. assert (Minimal R B x) as X. apply H3. clear X.

  (* And we assume that y is R-minimal in B. *)
  intros H4. assert (Minimal R B y) as X. apply H4. clear X.

  (* We need to show that x = y. *)
  assert (x = y) as X. 2: apply X.

  (* x is also an element of A. *)
  assert (A x) as H5. { apply H2. apply IsIn with R. assumption. }

  (* And y is an element of A. *)
  assert (A y) as H6. { apply H2. apply IsIn with R. assumption. }

  (* From the totality of R on A we see that x = y \/  x R y \/ y R x. *)
  specialize (H1 x y H5 H6).
  assert (x = y \/ R :(x,y): \/ R :(y,x):) as X. apply H1. clear X.

  (* We consider these three cases separately. *)
  destruct H1 as [H1|[H1|H1]].

  (* We first consider the case when x = y. *)
  - assert (x = y) as X. { apply H1. } clear X.

    (* Then we are done. *)
    assumption.

  (* We then consider the case x R y. *)
  - assert (R :(x,y):) as X. { apply H1. } clear X.

 (* This contradicts the minimality of y. *)
    assert (~R :(x,y):) as H7. { apply H4. apply IsIn with R. assumption. }

    contradiction.

  (* We finally consider the case y R x. *)
  - assert (R :(y,x):) as X. { apply H1. } clear X.

 (* This contradicts the minimality of x. *)
    assert (~R :(y,x):) as H7. { apply H3. apply IsIn with R. assumption. }

    contradiction.
Qed.

