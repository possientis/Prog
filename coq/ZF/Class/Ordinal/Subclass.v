Require Import ZF.Class.DiffBySet.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Order.E.
Require Import ZF.Class.Order.Isom.
Require Import ZF.Class.Order.Minimal.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.Enum.
Require Import ZF.Class.Ordinal.MinFresh.
Require Import ZF.Class.Ordinal.Monotone.
Require Import ZF.Class.Ordinal.Order.E.
Require Import ZF.Class.Proper.
Require Import ZF.Class.Relation.FunctionOn.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Ordinal.InfOfClass.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.ImageByClass.
Require Import ZF.Set.Relation.RestrictOfClass.

Require Import ZF.Notation.Eval.
Require Import ZF.Notation.Image.

Module CEN := ZF.Class.Ordinal.Enum.
Module CIN := ZF.Class.Incl.
Module CMF := ZF.Class.Ordinal.MinFresh.
Module COC := ZF.Class.Ordinal.Core.
Module COE := ZF.Class.Ordinal.Order.E.
Module COM := ZF.Class.Ordinal.Monotone.


(* MinFresh picks the E-minimal element of A not in the range of its argument.  *)
Definition MinFresh (A:Class) : Class := CMF.MinFresh E A.

(* The canonical isomorphism from On onto A when A is a subclass of On.         *)
Definition Enum (A:Class) : Class := CEN.Enum E A.

(* Enum A is a function class defined on the class of ordinals.                 *)
Proposition IsFunctionOn : forall (A:Class),
  FunctionOn (Enum A) On.
Proof.
  intros A. apply CEN.IsFunctionOn.
Qed.

(* Enum A is MinFresh-recursive.                                                *)
Proposition IsRecursive : forall (A:Class) (a:U),
  On a -> (Enum A)!a = (MinFresh A)!(Enum A :|: a).
Proof.
  intros A a H1. apply (CEN.IsRecursive E A). assumption.
Qed.

(* Each value of Enum A is the E-minimal element of A not yet covered.          *)
Proposition IsMinimal : forall (A:Class) (a:U),
  Proper A                                      ->
  A :<=: On                                     ->
  On a                                          ->
  Minimal E (A :\: (Enum A):[a]:) (Enum A)!a.
Proof.
  (* Proof by Claude. *)
  intros A a H1 H2 H3.
  assert (FunctionOn (Enum A) On) as H4. { apply IsFunctionOn. }
  assert (CEN.Recursive E A (Enum A)) as H5. { apply CEN.IsRecursive. }
  (* A minus the image of a under Enum A is non-empty since A is proper.        *)
  assert ((A :\: (Enum A):[a]:) :<>: :0:) as H6. {
    apply Proper.IsNotEmpty, DiffBySet.IsProper. assumption. }
  (* So Enum A(a) is the E-minimal element of that non-empty difference.        *)
  apply CEN.IsMinimal; try assumption.
  apply COE.IsWellFoundedWellOrd. assumption.
Qed.

Proposition IsInf : forall (A:Class) (a:U),
  Proper A                                      ->
  A :<=: On                                     ->
  On a                                          ->
  (Enum A)!a = inf (A :\: (Enum A):[a]:).
Proof.
  intros A a H1 H2 H3.
  apply InfOfClass.IsMinimal.
  - apply CIN.Tran with A. 2: assumption. apply DiffBySet.IsInclL.
  - apply Proper.IsNotEmpty, DiffBySet.IsProper. assumption.
  - apply IsMinimal; assumption.
Qed.

(* Enum A is an isomorphism from On to A.                                       *)
Proposition IsIsom : forall (A:Class),
  Proper A                  ->
  A :<=: On                 ->
  Isom (Enum A) E E On A.
Proof.
  intros A H1 H2. apply CEN.IsIsom; try assumption.
  apply COE.IsWellFoundedWellOrd. assumption.
Qed.

(* Enum A is the unique isomorphism from On to A.                               *)
Proposition IsUnique : forall (A G:Class),
  Proper A                  ->
  A :<=: On                 ->
  Isom G E E On A           ->
  G :~: Enum A.
Proof.
  intros A G H1 H2 H3. apply CEN.IsUnique; try assumption.
  apply COE.IsWellFoundedWellOrd. assumption.
Qed.

Proposition IsMonotone : forall (A:Class),
  Proper A                  ->
  A :<=: On                 ->
  Monotone (Enum A).
Proof.
  intros A H1 H2.
  apply COM.FromIsom with On A. 3: assumption.
  - apply IsIsom; assumption.
  - apply COC.IsOrdinal.
Qed.

(* A well ordered small class of ordinals is isomorphic to an ordinal.          *)
Proposition WhenSmall : forall (A:Class),
  Small A                                   ->
  A :<=: On                                 ->

  exists a, On a                            /\
    forall (g:U),
      g = (Enum A :|: a)                    ->
      Isom (toClass g) E E (toClass a) A.
Proof.
  intros A H1 H2. apply CEN.WhenSmall. 1: assumption.
  apply COE.IsWellOrdering. assumption.
Qed.

