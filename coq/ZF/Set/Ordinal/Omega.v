Require Import ZF.Class.Complement.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.Ordinal.Omega.
Require Import ZF.Class.Ordinal.Transitive.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Limit.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.Ordinal.NonLimit.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Ordinal.Transitive.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Single.
Export ZF.Notation.N.

(* The set defined by the small class N. The set of natural numbers 0,1,2,...   *)
Definition omega : U := fromClass :N Omega.IsSmall.

(* Notation ":N" := omega                                                       *)
Global Instance SetN : N U := { omega := omega }.

(* Converting the set N to a class yields the class N.                          *)
Proposition ToClass : toClass :N :~: :N.
Proof.
  apply ToFromClass.
Qed.

(* A natural number is an ordinal whose successor contains non-limit ordinals.  *)
Proposition Charac : forall (n:U),
  n :< :N <-> Ordinal n /\ toClass (succ n) :<=: NonLimit.
Proof.
  intros n. split; intros H1.
  - apply FromClass.Charac in H1. assumption.
  - apply FromClass.Charac. assumption.
Qed.

(* An ordinal is a natural number iff every lesser ordinal is a non-limit ord   *)
Proposition Charac2 : forall (n:U), Ordinal n ->
  n :< :N <-> forall (a:U), Ordinal a -> a :<=: n -> NonLimit a.
Proof.
  intros n H1. split; intros H2.
  - apply FromClass.Charac in H2. apply Class.Ordinal.Omega.Charac; assumption.
  - apply FromClass.Charac. apply Class.Ordinal.Omega.Charac; assumption.
Qed.

(* 0 is a natural number.                                                       *)
Proposition HasZero : :0: :< :N.
Proof.
  apply FromClass.Charac, Class.Ordinal.Omega.HasZero.
Qed.

(* The successor of a natural number is a natural number.                       *)
Proposition HasSucc : forall (n:U), n :< :N -> succ n :< :N.
Proof.
  intros n H1. apply FromClass.Charac in H1. apply FromClass.Charac.
  apply Class.Ordinal.Omega.HasSucc. assumption.
Qed.

(* The set N is not empty.                                                      *)
Proposition IsNotEmpty : :N <> :0:.
Proof.
  intros H1. apply Empty.Charac with :0:.
  assert (:0: :< :N) as H2. { apply HasZero. }
  rewrite H1 in H2. assumption.
Qed.

(* N is a transitive set.                                                       *)
Proposition IsTransitive : Transitive :N.
Proof.
  apply Transitive.EquivCompat with :N.
  - apply Equiv.Sym, ToClass.
  - apply Class.Ordinal.Omega.IsTransitive.
Qed.

(* The set N is an ordinal.                                                     *)
Proposition IsOrdinal : Ordinal :N.
Proof.
  apply Core.EquivCompat with :N.
  - apply Equiv.Sym, ToClass.
  - apply Class.Ordinal.Omega.IsOrdinal.
Qed.

(* Every element of N is an ordinal.                                            *)
Proposition HasOrdinalElem : toClass :N :<=: Ordinal.
Proof.
  intros n H1. apply Charac in H1. destruct H1 as [H1 _]. assumption.
Qed.

(* Every element of N is a non-limit ordinal.                                   *)
Proposition HasNonLimitElem : toClass :N :<=: NonLimit.
Proof.
  intros n H1. apply Charac in H1. destruct H1 as [_ H1]. apply H1, Succ.IsIn.
Qed.

(* The set N is a limit ordinal.                                                *)
Proposition IsLimit : Limit :N.
Proof.
  split.
  - apply IsOrdinal.
  - intros H1. apply NoElemLoop1 with :N. apply Charac. split.
    + apply IsOrdinal.
    + intros n H2. apply Union2.Charac in H2. destruct H2 as [H2|H2].
      * apply HasNonLimitElem. assumption.
      * apply Single.Charac in H2. subst. assumption.
Qed.

(* A limit ordinal is no less than N.                                           *)
Proposition IsInclInLimit : forall (a:U), Limit a -> :N :<=: a.
Proof.
  intros a H1. assert (a :< :N \/ :N :<=: a) as H2. {
    apply ElemOrIncl.
    - apply Limit.HasOrdinalElem. assumption.
    - apply IsOrdinal. }
  destruct H2 as [H2|H2]. 2: assumption. exfalso.
  apply H1. apply Charac in H2. apply H2, Succ.IsIn.
Qed.

(* An ordinal with non-limit ordinals as elements is a subset of N.             *)
Proposition IsIncl : forall (a:U),
  Ordinal a               ->
  toClass a :<=: NonLimit ->
  a :<=: :N.
Proof.
  intros a H1 H2. apply Incl.EquivCompatR with :N.
  - apply Equiv.Sym, ToClass.
  - apply Class.Ordinal.Omega.IsIncl; assumption.
Qed.

(* Principle of induction over the natural numbers.                             *)
Proposition Induction : forall (A:Class),
  A :0:                                     ->
  (forall n, n :< :N -> A n -> A (succ n))  ->
  toClass :N :<=: A.
Proof.
  intros A H1 H2. apply Incl.EquivCompatL with :N.
  - apply Equiv.Sym, ToClass.
  - apply Class.Ordinal.Omega.Induction. 1: assumption.
    intros n H3. apply H2. apply FromClass.Charac. assumption.
Qed.

(* Principle of induction over the natural numbers.                             *)
Proposition FiniteInduction : forall (A:Class),
  A :<=: toClass :N             ->
  A :0:                         ->
  (forall n, A n -> A (succ n)) ->
  A :~: toClass :N.
Proof.
  intros A H1 H2 H3. apply Equiv.Tran with :N. 2: { apply Equiv.Sym, ToClass. }
  apply Class.Ordinal.Omega.FiniteInduction; try assumption.
  apply Incl.EquivCompatR with (toClass :N). 2: assumption. apply ToClass.
Qed.

(* A non-empty subclass of N has a minimal element.                             *)
Proposition HasMinimal : forall (A:Class),
  A :<=: toClass :N   ->
  A :<>: :0:          ->
  exists m, A m /\
    forall n, A n -> m :<=: n.
Proof.
  intros A H1 H2.
  assert (exists m, Ordinal m /\ A m /\forall n, A n -> m :<=: n) as H3. {
    apply Core.HasMinimal. 2: assumption.
    intros x H3. apply HasOrdinalElem, H1. assumption. }
  destruct H3 as [m [H3 [H4 H5]]]. exists m. split; assumption.
Qed.

(* A non-empty subset of N has a minimal element.                               *)
Proposition HasMinimal2 : forall (a:U),
  a :<=: :N             ->
  a <> :0:              ->
  exists m, m :< a /\
    forall n, n :< a -> m :<=: n.
Proof.
  intros a H1 H2. apply HasMinimal. 1: assumption.
  apply NotEmptyToClass. assumption.
Qed.
