Require Import ZF.Class.
Require Import ZF.Set.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Pair.
Require Import ZF.Set.Singleton.
Require Import ZF.Set.Tuple.
Require Import ZF.Set.Union2.

Require Import ZF.Set.Empty.
Export ZF.Set.Empty.

Require Import ZF.Notation.One.
Export ZF.Notation.One.

Require Import ZF.Notation.Two.
Export ZF.Notation.Two.

Require Import ZF.Notation.Three.
Export ZF.Notation.Three.

Require Import ZF.Notation.Four.
Export ZF.Notation.Four.

Require Import ZF.Notation.Five.
Export ZF.Notation.Five.

Definition zero : U := :0:.

Definition one  : U := succ :0:.

(* Notation ":1:" := one                                                        *)
Global Instance SetOne : One U := { one := one }.

Definition two  : U := succ :1:.

(* Notation ":2:" := two                                                        *)
Global Instance SetTwo : Two U := { two := two }.

Definition three  : U := succ :2:.

(* Notation ":3:" := three                                                      *)
Global Instance SetThree : Three U := { three := three }.

Definition four  : U := succ :3:.

(* Notation ":4:" := four                                                       *)
Global Instance SetFour : Four U := { four := four }.

Definition five  : U := succ :4:.

(* Notation ":5:" := five                                                       *)
Global Instance SetFive : Five U := { five := five }.

Proposition ZeroIsOrdinal : Ordinal :0:.
Proof.
  apply Ordinal.EquivCompat with :0:. 2: apply Class.Ordinal.ZeroIsOrdinal.
  apply EquivSym, ToClassOfEmptySet.
Qed.

Proposition OneIsOrdinal : Ordinal :1:.
Proof.
  apply SuccIsOrdinal, ZeroIsOrdinal.
Qed.

Proposition TwoIsOrdinal : Ordinal :2:.
Proof.
  apply SuccIsOrdinal, OneIsOrdinal.
Qed.

Proposition ThreeIsOrdinal : Ordinal :3:.
Proof.
  apply SuccIsOrdinal, TwoIsOrdinal.
Qed.

Proposition FourIsOrdinal : Ordinal :4:.
Proof.
  apply SuccIsOrdinal, ThreeIsOrdinal.
Qed.

Proposition FiveIsOrdinal : Ordinal :5:.
Proof.
  apply SuccIsOrdinal, FourIsOrdinal.
Qed.

Proposition TwoExtension : :2: = :{ :0:, :1: }:.
Proof.
Admitted.

Proposition TreeExtension : :3: = :{ :0:, :1:, :2: }:.
Proof.
  apply DoubleInclusion. split; intros x H1; apply Union2Charac;
  apply Union2Charac in H1; destruct H1 as [H1|H1].
  - left. rewrite TwoExtension in H1. assumption.
  - right.  assumption.
  - left. rewrite TwoExtension. assumption.
  - right. assumption.
 Qed. 
