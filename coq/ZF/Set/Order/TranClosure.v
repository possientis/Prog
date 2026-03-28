Require Import ZF.Class.Incl.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Order.TranClosure.
Require Import ZF.Class.Order.WellFounded.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Omega.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.Fun.


Module COT := ZF.Class.Order.TranClosure.

(* An R-transitive set a in class A,                                            *)
Definition Transitive (R A:Class) (a:U) : Prop := COT.Transitive R A a.

(* The R-transitive closure of a in A.                                          *)
Definition closure (R A:Class) (a:U) : U :=
  fromClass (COT.closure R A a) (COT.IsSmall R A a).

Lemma IsClosure : forall (R A:Class) (a:U),
  WellFounded R A                       ->
  toClass a :<=: A                      ->
  COT.IsClosure R A a (closure R A a).
Proof.
  intros R A a H1 H2.
  assert (exists b, IsClosure R A a b) as H3. { apply COT.Exists; assumption. }
  destruct H3 as [b H3].
  assert (b = closure R A a) as H4. {
    apply DoubleInclusion. split; intros x H4.
    - apply FromClass.Charac. exists b. split; assumption.
    - apply FromClass.Charac in H4. destruct H4 as [c [H4 H5]].
      assert (b = c) as H6. { apply COT.IsUnique with R A a; assumption. }
      subst. assumption. }
  subst. assumption.
Qed.

(* The R-transitive closure of a in A contains (all elemnts of) a.              *)
Proposition Contains : forall (R A:Class) (a:U),
  WellFounded R A                       ->
  toClass a :<=: A                      ->
  a :<=: closure R A a.
Proof.
  intros R A a H1 H2. apply COT.Contains with R A, IsClosure; assumption.
Qed.

(* The R-transitive closure of a in A is a subset of A.                         *)
Proposition IsIncl : forall (R A:Class) (a:U),
  WellFounded R A                       ->
  toClass a :<=: A                      ->
  toClass (closure R A a) :<=: A.
Proof.
  intros R A a H1 H2. apply COT.IsIncl with R a, IsClosure; assumption.
Qed.

(* The R-transitive closure of a in A is R-transitive in A..                    *)
Proposition IsTransitive : forall (R A:Class) (a:U),
  WellFounded R A                       ->
  toClass a :<=: A                      ->
  Transitive R A (closure R A a).
Proof.
  intros R A a H1 H2. apply COT.IsTransitive with a, IsClosure; assumption.
Qed.

Proposition DecreasingPath : forall (R A:Class) (a x:U),
  WellFounded R A                               ->
  toClass a :<=: A                              ->
  x :< closure R A a                            ->
  exists n g,
    n :< :N                                     /\
    Fun g (succ n) (closure R A a)              /\
    g!:0: :< a                                  /\
    g!n = x                                     /\
    (forall i, i :< n -> R :(g!(succ i),g!i):).
Proof.
  intros R A a x H1 H2 H3.
  apply COT.DecreasingPath with A. 2: assumption.
  apply IsClosure; assumption.
Qed.

(* The R-transitive closure in A is the smallest R-transitive set such that ... *)
Proposition IsSmallest : forall (R A:Class) (a b:U),
  WellFounded R A       ->
  toClass a :<=: A      ->
  a :<=: b              ->
  toClass b :<=: A      ->
  Transitive R A b      ->
  closure R A a :<=: b.
Proof.
  intros R A a b H1 H2. apply COT.IsSmallest, IsClosure; assumption.
Qed.


