Require Import ZF.Class.Core.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.NonLimit.
Require Import ZF.Set.Core.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Single.
Require Import ZF.Set.Union2.

Require Import ZF.Notation.N.
Export ZF.Notation.N.

(* The class natural numbers.                                                   *)
Definition omega : Class := fun a =>
  Ordinal a /\ toClass (succ a) :<=: NonLimit.

(* Notation ":N" := omega                                                       *)
Global Instance ClassN : N Class := { omega := omega }.

(* N is a class of ordinals.                                                    *)
Proposition IsClassOfOrdinals : :N :<=: On.
Proof.
  intros a [H1 _]. assumption.
Qed.

(* N is a class of non-limit ordinals.                                          *)
Proposition IsClassOfNonLimits : :N :<=: NonLimit.
Proof.
  intros a [H1 H2]. apply H2. apply ElemSucc.
Qed.

(* 0 belongs to N. The type annotation is needed here for instance resolution.  *)
Proposition HasZero : (:N : Class) :0:.
Proof.
  split.
  - apply ZeroIsOrdinal.
  - intros a H1. apply Union2.Charac in H1. destruct H1 as [H1|H1].
    + apply Empty.Charac in H1. contradiction.
    + apply Single.Charac in H1. subst. left. reflexivity.
Qed.

(* If a is a natural number, then so is succ a.                                 *)
Proposition HasSucc : forall (a:U), (:N : Class) a -> (:N : Class) (succ a).
Proof.
  intros a [H1 H2]. split.
  - apply SuccIsOrdinal. assumption.
  - intros b H3. apply Union2.Charac in H3. destruct H3 as [H3|H3].
    + apply H2. assumption.
    + apply Single.Charac in H3. subst. right. exists a. split.
      * assumption.
      * reflexivity.
Qed.

(* N is not an empty class.                                                     *)
Proposition NotEmpty : :N :<>: :0:.
Proof.
  intros H1. apply Class.Empty.Charac with :0:. apply H1, HasZero.
Qed.

(* Characterisation of the elements of N.                                       *)
Proposition Charac : forall (a:U), Ordinal a ->
  :N a <-> forall (b:U), Ordinal b -> b :<=: a -> NonLimit b.
Proof.
  intros a H1. split; intros H2.
  - destruct H2 as [H2 H3]. intros b H4 H5. apply H3.
    apply InclElemTran with a; try assumption.
    + apply SuccIsOrdinal. assumption.
    + apply ElemSucc.
  - split. 1: assumption. intros b H3. assert (Ordinal b) as H4. {
      apply ElemIsOrdinal with (succ a). 2: assumption.
      apply SuccIsOrdinal. assumption. }
    apply H2. 1: assumption.
    assert (a :< b \/ b :<=: a) as H5. { apply ElemOrIncl; assumption. }
    destruct H5 as [H5|H5]. 2: assumption.
    exfalso. apply NothingInBetween with a b. split; assumption.
Qed.

Proposition IsSubClass : forall (a:U), Ordinal a ->
  toClass a :<=: NonLimit -> toClass a :<=: :N.
Proof.
  intros a H1 H2 b H3. split.
  - apply ElemIsOrdinal with a; assumption.
  - intros c H4. assert (Ordinal b) as H5. {
      apply ElemIsOrdinal with a; assumption. }
    assert (Ordinal c) as H6. {
      apply ElemIsOrdinal with (succ b). 2: assumption.
      apply SuccIsOrdinal. assumption. }
    apply H2. apply InclElemTran with b; try assumption.
Admitted.
