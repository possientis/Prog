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

Require Import ZF.Notation.Six.
Export ZF.Notation.Six.

Require Import ZF.Notation.Seven.
Export ZF.Notation.Seven.

Require Import ZF.Notation.Eight.
Export ZF.Notation.Eight.

Require Import ZF.Notation.Nine.
Export ZF.Notation.Nine.

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

Definition six : U := succ :5:.

(* Notation ":6:" := six                                                        *)
Global Instance SetSix : Six U := { six := six }.

Definition seven : U := succ :6:.

(* Notation ":7:" := seven                                                      *)
Global Instance SetSeven : Seven U := { seven := seven }.

Definition eight : U := succ :7:.

(* Notation ":8:" := eight                                                      *)
Global Instance SetEight : Eight U := { eight := eight }.

Definition nine : U := succ :8:.

(* Notation ":9:" := nine                                                      *)
Global Instance SetNine : Nine U := { nine := nine }.

Proposition ZeroIsOrdinal : Ordinal :0:.
Proof.
  apply Class.Ordinal.Core.EquivCompat with :0:.
  2: apply Class.Ordinal.Core.ZeroIsOrdinal.
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

Proposition SixIsOrdinal : Ordinal :6:.
Proof.
  apply SuccIsOrdinal, FiveIsOrdinal.
Qed.

Proposition SevenIsOrdinal : Ordinal :7:.
Proof.
  apply SuccIsOrdinal, SixIsOrdinal.
Qed.

Proposition EightIsOrdinal : Ordinal :8:.
Proof.
  apply SuccIsOrdinal, SevenIsOrdinal.
Qed.

Proposition NineIsOrdinal : Ordinal :9:.
Proof.
  apply SuccIsOrdinal, EightIsOrdinal.
Qed.

Proposition OneExtension : :1: = :{ :0: }:.
Proof.
  assert (:0: :\/: :{ :0: }: = :{ :0: }:) as H1. { apply Union2IdentityL. }
  rewrite <- H1. reflexivity.
Qed.

Proposition TwoExtension : :2: = :{ :0:, :1: }:.
Proof.
  rewrite PairAsUnion2, <- OneExtension. reflexivity.
Qed.

Proposition ThreeExtension : :3: = :{ :0:, :1:, :2: }:.
Proof.
  unfold tuple3. rewrite <- TwoExtension. reflexivity.
Qed.

Proposition FourExtension : :4: = :{ :0:, :1:, :2:, :3: }:.
Proof.
  unfold tuple4. rewrite <- ThreeExtension. reflexivity.
Qed.

