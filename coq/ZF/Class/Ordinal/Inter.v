Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Core.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.Transitive.
Require Import ZF.Set.Core.
Require Import ZF.Set.Ordinal.Core.

(* The intersection of a non-empty class of ordinals is a class of ordinals.    *)
Proposition IsIncl : forall (A:Class), A :<=: On -> A :<>: :0: -> :I(A) :<=: On.
Proof.
  intros A H1 H2. apply Class.Empty.HasElem in H2. destruct H2 as [a H2].
  intros x H3. apply Core.IsOrdinal with a.
  - apply H1. assumption.
  - apply H3. assumption.
Qed.

(* The (tweaked) intersection of a class of ordinals is a class of ordinals.    *)
Proposition IsIncl' : forall (A:Class), A :<=: On -> :J(A) :<=: On.
Proof.
  intros A H1.
  assert (A :~: :0: \/ A :<>: :0:) as H2. {
    apply LawExcludedMiddle. }
  destruct H2 as [H2|H2].
  - apply Incl.EquivCompatL with :0:.
    + apply EquivSym, Inter.WhenEmpty. assumption.
    + intros x H3. contradiction.
  - apply Incl.EquivCompatL with :I(A).
    + apply EquivSym, Inter.WhenNotEmpty. assumption.
    + apply IsIncl; assumption.
Qed.

(* The intersection of a class of ordinals is a transitive class.               *)
Proposition IsTransitive : forall (A:Class), A :<=: On -> Transitive :I(A).
Proof.
  intros A H1 y H2 x H3 z H4.
  assert (y :< z) as H5. { apply H2. assumption. }
  assert (Ordinal z) as H6. { apply H1. assumption. }
  assert (Ordinal y) as H7. { apply Core.IsOrdinal with z; assumption. }
  assert (Ordinal x) as H8. { apply Core.IsOrdinal with y; assumption. }
  apply ElemElemTran with y; assumption.
Qed.

(* The (tweaked) intersection of a class of ordinals is a transitive class.     *)
Proposition IsTransitive' : forall (A:Class), A :<=: On -> Transitive :J(A).
Proof.
  intros A H1.
  assert (A :~: :0: \/ A :<>: :0:) as H2. {
    apply LawExcludedMiddle. }
  destruct H2 as [H2|H2].
  - apply Transitive.EquivCompat with :0:.
    + apply EquivSym, Inter.WhenEmpty. assumption.
    + intros x H3. contradiction.
  - apply Transitive.EquivCompat with :I(A).
    + apply EquivSym, Inter.WhenNotEmpty. assumption.
    + apply IsTransitive. assumption.
Qed.

(* The intersection of a non-empty class of ordinals is an ordinal class.       *)
Proposition IsOrdinal : forall (A:Class),
  A :<=: On -> A :<>: :0: -> Class.Ordinal.Core.Ordinal :I(A).
Proof.
  intros A H1 H2. apply TransitiveInclIsOrdinal with On.
  - apply OnIsOrdinal.
  - apply IsTransitive. assumption.
  - apply IsIncl; assumption.
Qed.

(* The (tweaked) intersection of class of ordinals is an ordinal class.         *)
Proposition IsOrdinal' : forall (A:Class),
  A :<=: On -> Class.Ordinal.Core.Ordinal :J(A).
Proof.
  intros A H1.
  assert (A :~: :0: \/ A :<>: :0:) as H2. {
    apply LawExcludedMiddle. }
  destruct H2 as [H2|H2].
  - apply Class.Ordinal.Core.EquivCompat with :0:.
    + apply EquivSym, Inter.WhenEmpty. assumption.
    + apply Class.Ordinal.Core.ZeroIsOrdinal.
  - apply Class.Ordinal.Core.EquivCompat with :I(A).
    + apply EquivSym, WhenNotEmpty. assumption.
    + apply IsOrdinal; assumption.
Qed.

(* The intersection of a non-empty class of ordinals is a lower-bound.          *)
Proposition IsLowerBound : forall (A:Class) (a:U),
  A :<=: On  -> A a -> :I(A) :<=: toClass a.
Proof.
  intros A a H1 H2 x H3. apply H3. assumption.
Qed.

(* The (tweaked) intersection of a class of ordinals is a lower-bound.          *)
Proposition IsLowerBound' : forall (A:Class) (a:U),
  A :<=: On -> A a -> :J(A) :<=: toClass a.
Proof.
  intros A a H1 H2.
  assert (A :~: :0: \/ A :<>: :0:) as H3. {
    apply LawExcludedMiddle. }
  destruct H3 as [H3|H3].
  - apply Incl.EquivCompatL with :0:.
    + apply EquivSym, Inter.WhenEmpty. assumption.
    + intros x H4. contradiction.
  - apply Incl.EquivCompatL with :I(A).
    + apply EquivSym, WhenNotEmpty. assumption.
    + apply IsLowerBound; assumption.
Qed.

(* The intersection of a non-empty class of ordinals is the largest lower-bound.*)
Proposition IsLargest : forall (A:Class) (a:U),
  A :<=: On                     ->
  A :<>: :0:                    ->
  (forall b, A b  -> a :<=: b)  ->
  toClass a :<=: :I(A).
Proof.
  intros A a H1 H2 H3 x H4 b H5. apply H3; assumption.
Qed.

(* The non-empty assumption is needed here even foe the twaked case..           *)
Proposition IsLargest' : forall (A:Class) (a:U),
  A :<=: On                     ->
  A :<>: :0:                    ->
  (forall b, A b  -> a :<=: b)  ->
  toClass a :<=: :J(A).
Proof.
  intros A a H1 H2 H3. apply Incl.EquivCompatR with :I(A).
  - apply EquivSym, Inter.WhenNotEmpty. assumption.
  - apply IsLargest; assumption.
Qed.
