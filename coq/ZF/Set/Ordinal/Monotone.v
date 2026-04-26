Require Import ZF.Class.Equiv.
Require Import ZF.Class.Ordinal.Monotone.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Order.E.
Require Import ZF.Set.Order.Isom.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.OrdFun.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.

Module COI := ZF.Class.Order.Isom.
Module COM := ZF.Class.Ordinal.Monotone.
Module SOE := ZF.Set.Order.E.


(* A strictly monotone ordinal function.                                        *)
Definition Monotone (f:U) : Prop := OrdFun f  /\ forall (a b:U),
  a :< domain f -> b :< domain f -> a :< b  -> f!a :< f!b.

Proposition ToClass : forall (f:U),
  Monotone f -> COM.Monotone (toClass f).
Proof.
  intros f [H1 H2]. split.
  - apply OrdFun.ToClass. assumption.
  - intros a b H3 H4 H5. apply H2. 3: assumption.
    + apply Domain.ToClass. assumption.
    + apply Domain.ToClass. assumption.
Qed.

Proposition FromClass : forall (f:U),
  COM.Monotone (toClass f) -> Monotone f.
Proof.
  intros f [H1 H2]. split.
  - apply OrdFun.FromClass. assumption.
  - intros a b H3 H4 H5. apply H2. 3: assumption.
    + apply Domain.ToClass. assumption.
    + apply Domain.ToClass. assumption.
Qed.

Proposition IsIncl : forall (f a:U),
  Monotone f -> a :< domain f -> a :<=: f!a.
Proof.
  intros f a H1 H2. apply COM.IsIncl.
  - apply ToClass. assumption.
  - apply Domain.ToClass. assumption.
Qed.

Proposition FromIsom : forall (f a b:U),
  Ordinal a                         ->
  (forall x, x :< b -> Ordinal x)   ->
  Isom f (E a) (E b) a b            ->
  Monotone f.
Proof.
  intros f a b H1 H2 H3.
  apply FromClass.
  apply COM.FromIsom with (toClass a) (toClass b). 3: assumption.
  - apply (COI.RestrictL _ _ _ (toClass a)).
    apply (COI.RestrictR _ _ _ _ (toClass b)).
    apply COI.EquivCompat2 with (toClass (E a)).
    + apply SOE.ToClass.
    + apply COI.EquivCompat3 with (toClass (E b)).
      * apply SOE.ToClass.
      * apply Isom.ToClass. assumption.
  - apply Core.ToClass. assumption.
Qed.
