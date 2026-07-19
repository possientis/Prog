Require Import ZF.Class.Equiv.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Pair.
Require Import ZF.Set.Single.
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

(* Notation ":9:" := nine                                                       *)
Global Instance SetNine : Nine U := { nine := nine }.

(* Zero is an ordinal.                                                          *)
Proposition Zero : Ordinal :0:.
Proof.
  apply Core.Zero.
Qed.

(* One is an ordinal.                                                           *)
Proposition OneIsOrdinal : Ordinal :1:.
Proof.
  apply Succ.IsOrdinal, Zero.
Qed.

(* Two is an ordinal.                                                           *)
Proposition TwoIsOrdinal : Ordinal :2:.
Proof.
  apply Succ.IsOrdinal, OneIsOrdinal.
Qed.

(* Three is an ordinal.                                                         *)
Proposition ThreeIsOrdinal : Ordinal :3:.
Proof.
  apply Succ.IsOrdinal, TwoIsOrdinal.
Qed.

(* Four is an ordinal.                                                          *)
Proposition FourIsOrdinal : Ordinal :4:.
Proof.
  apply Succ.IsOrdinal, ThreeIsOrdinal.
Qed.

(* Five is an ordinal.                                                          *)
Proposition FiveIsOrdinal : Ordinal :5:.
Proof.
  apply Succ.IsOrdinal, FourIsOrdinal.
Qed.

(* Six is an ordinal.                                                           *)
Proposition SixIsOrdinal : Ordinal :6:.
Proof.
  apply Succ.IsOrdinal, FiveIsOrdinal.
Qed.

(* Seven is an ordinal.                                                         *)
Proposition SevenIsOrdinal : Ordinal :7:.
Proof.
  apply Succ.IsOrdinal, SixIsOrdinal.
Qed.

(* Eight is an ordinal.                                                         *)
Proposition EightIsOrdinal : Ordinal :8:.
Proof.
  apply Succ.IsOrdinal, SevenIsOrdinal.
Qed.

(* Nine is an ordinal.                                                          *)
Proposition NineIsOrdinal : Ordinal :9:.
Proof.
  apply Succ.IsOrdinal, EightIsOrdinal.
Qed.

(* The set 1 equals the singleton containing 0.                                 *)
Proposition OneExtension : :1: = :{ :0: }:.
Proof.
  assert (:0: :\/: :{ :0: }: = :{ :0: }:) as H1. { apply Union2.IdentityL. }
  rewrite <- H1. reflexivity.
Qed.

(* The set 2 equals the pair containing 0 and 1.                                *)
Proposition TwoExtension : :2: = :{ :0:, :1: }:.
Proof.
  rewrite PairAsUnion2, <- OneExtension. reflexivity.
Qed.

(* The set 3 equals the triple containing 0, 1 and 2.                           *)
Proposition ThreeExtension : :3: = :{ :0:, :1:, :2: }:.
Proof.
  unfold tuple3. rewrite <- TwoExtension. reflexivity.
Qed.

(* The set 4 equals the quadruple containing 0, 1, 2 and 3.                     *)
Proposition FourExtension : :4: = :{ :0:, :1:, :2:, :3: }:.
Proof.
  unfold tuple4. rewrite <- ThreeExtension. reflexivity.
Qed.

(* Zero and one are distinct.                                                   *)
Proposition ZeroIsNotOne : :0: <> :1:.
Proof.
  intros H1. symmetry in H1. revert H1. apply Succ.NotEqual.
Qed.

(* One is not a subset of zero.                                                 *)
Proposition OneNotLessThanZero : ~ :1: :<=: (:0: : U).
Proof.
  intros H1.
  assert (:0: :< :0:) as H2. { apply H1, Succ.IsIn. }
  apply Empty.Charac in H2. contradiction.
Qed.

(* A non-zero ordinal either equals 1 or contains 1.                            *)
Proposition OneOrElem : forall (a:U), Ordinal a ->
  :0: :< a -> a = :1: \/ :1: :< a.
Proof.
  intros a H1 H2.
  assert (:1: :< a \/ a :<=: :1:) as H3. {
    apply Core.ElemOrIncl. 2: assumption. apply OneIsOrdinal. }
  destruct H3 as [H3|H3].
  - right. assumption.
  - left. apply Incl.Double. split. 1: assumption.
    intros x H4. apply Succ.Charac in H4. destruct H4 as [H4|H4].
    + subst. assumption.
    + apply Empty.Charac in H4. contradiction.
Qed.

(* An ordinal that contains 1 as a subset also contains 0 as an element.        *)
Proposition HasZero : forall (a:U), Ordinal a ->
  :1: :<=: a -> :0: :< a.
Proof.
  intros a H1 H2. apply H2, Succ.IsIn.
Qed.

(* An ordinal that contains 0 as an element also contains 1 as a subset.        *)
Proposition HasZeroRev : forall (a:U), Ordinal a ->
  :0: :< a -> :1: :<=: a.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a H1 H2.
  apply OneOrElem in H2. 2: assumption. destruct H2 as [H2|H2].
  - subst. apply Incl.Refl.
  - apply Core.ElemIsIncl; assumption.
Qed.

