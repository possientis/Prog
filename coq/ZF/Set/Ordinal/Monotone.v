Require Import ZF.Class.Equiv.
Require Import ZF.Class.Ordinal.Monotone.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Order.Isom.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Order.E.
Require Import ZF.Set.Ordinal.OrdFun.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Relation.Compose.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.Fun.
Require Import ZF.Set.Relation.Fun.IfThenElse.
Require Import ZF.Set.Relation.FunctionOn.
Require Import ZF.Set.Relation.Id.
Require Import ZF.Set.Relation.RestrictOfClass.

Module COI := ZF.Class.Order.Isom.
Module CRD := ZF.Class.Relation.Domain.
Module COM := ZF.Class.Ordinal.Monotone.
Module SFI := ZF.Set.Relation.Fun.IfThenElse.
Module SOE := ZF.Set.Ordinal.Order.E.


(* A strictly monotone ordinal function.                                        *)
Definition Monotone (f:U) : Prop := OrdFun f  /\ forall (a b:U),
  a :< domain f -> b :< domain f -> a :< b  -> f!a :< f!b.

(* The empty set is a strictly monotone ordinal function.                       *)
Proposition WhenZero : forall (f:U),
  f = :0: -> Monotone f.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros f H1. split.
  - (* The empty relation is an ordinal function.                               *)
    apply OrdFun.WhenZero. assumption.
  - (* There are no elements in its domain, so order preservation is vacuous.   *)
    intros a b H2 H3 H4.
    assert (domain f = :0:) as H5. { apply Domain.WhenZero. assumption. }
    rewrite H5 in H2. apply Empty.Charac in H2. contradiction.
Qed.

(* If the set is monotone, then so is the class.                                *)
Proposition ToClass : forall (f:U),
  Monotone f -> COM.Monotone (toClass f).
Proof.
  intros f [H1 H2]. split.
  - apply OrdFun.ToClass. assumption.
  - intros a b H3 H4 H5. apply H2. 3: assumption.
    + apply Domain.ToClass. assumption.
    + apply Domain.ToClass. assumption.
Qed.

(* If the class is monotone, then so is the set.                                *)
Proposition FromClass : forall (f:U),
  COM.Monotone (toClass f) -> Monotone f.
Proof.
  intros f [H1 H2]. split.
  - apply OrdFun.FromClass. assumption.
  - intros a b H3 H4 H5. apply H2. 3: assumption.
    + apply Domain.ToClass. assumption.
    + apply Domain.ToClass. assumption.
Qed.

(* Restricting a class monotone function to an ordinal is monotone.             *)
Proposition ClassRestrict : forall (F:Class) (a:U),
  Ordinal a                     ->
  COM.Monotone F                ->
  toClass a :<=: CRD.domain F   ->
  Monotone (F:|:a).
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros F a H1 [H2 H3] H4. split.
  - apply OrdFun.ClassRestrict; assumption.
  - intros x y H5 H6 H7.
    (* Values of the restriction agree with the class values on its domain.     *)
    assert (domain (F:|:a) = a) as H8. {
      apply RestrictOfClass.DomainWhenIncl. 2: assumption.
      destruct H2 as [[_ H2] _]. apply H2. }
    rewrite H8 in H5. rewrite H8 in H6.
    assert ((F:|:a)!x = F!x) as H9. {
      apply RestrictOfClass.Eval. 2: assumption.
      destruct H2 as [[_ H2] _]. apply H2. }
    assert ((F:|:a)!y = F!y) as H10. {
      apply RestrictOfClass.Eval. 2: assumption.
      destruct H2 as [[_ H2] _]. apply H2. }
    rewrite H9, H10.
    apply H3; try assumption; apply H4; assumption.
Qed.

(* A strictly monotone ordinal function satisfies a <= f(a) for all a.          *)
Proposition IsIncl : forall (f a:U),
  Monotone f -> a :< domain f -> a :<=: f!a.
Proof.
  intros f a H1 H2. apply COM.IsIncl.
  - apply ToClass. assumption.
  - apply Domain.ToClass. assumption.
Qed.

(* A strictly monotone ordinal function is weakly monotone.                     *)
Proposition Relax : forall (f x y:U),
  Monotone f     ->
  x :< domain f  ->
  y :< domain f  ->
  x :<=: y       ->
  f!x :<=: f!y.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros f x y H1 H2 H3 H4.
  assert (Ordinal (domain f)) as H5. { apply OrdFun.DomainOf. apply H1. }
  assert (Ordinal x) as H6. { apply Core.IsOrdinal with (domain f); assumption. }
  assert (Ordinal y) as H7. { apply Core.IsOrdinal with (domain f); assumption. }
  assert (Ordinal f!y) as H8. { apply OrdFun.IsOrdinal. 1: apply H1. assumption. }
  assert (x = y \/ x :< y) as H9. { apply Core.EqualOrElem; assumption. }
  destruct H9 as [H9|H9].
  - (* Equal arguments have equal values.                                       *)
    subst. apply Incl.Refl.
  - (* A strictly larger argument gives a strictly larger value.                *)
    apply Core.ElemIsIncl. 1: assumption. apply H1; assumption.
Qed.

(* A function between ordinals is monotone when it preserves membership.        *)
Proposition FromFun : forall (f a b:U),
  Ordinal a                                                   ->
  Ordinal b                                                   ->
  Fun f a b                                                   ->
  (forall x y, x :< a -> y :< a -> x :< y -> f!x :< f!y)      ->
  Monotone f.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros f a b H1 H2 H3 H4. destruct H3 as [H3 H5]. split.
  - (* The domain is the source ordinal and all values lie in the target.       *)
    split. 1: apply H3. split.
    + assert (domain f = a) as H6. { apply H3. }
      rewrite H6. assumption.
    + intros y H6. apply Core.IsOrdinal with b. 1: assumption. apply H5.
      assumption.
  - (* Order preservation over the domain is the displayed hypothesis.          *)
    intros x y H6 H7 H8.
    assert (domain f = a) as H9. { apply H3. }
    rewrite H9 in H6. rewrite H9 in H7. apply H4; assumption.
Qed.

(* The identity on an ordinal is a strictly monotone ordinal function.          *)
Proposition WhenId : forall (a:U),
  Ordinal a -> Monotone (id a).
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a H1.
  apply FromFun with a a; try assumption. 1: apply Id.IsFun.
  intros x y H2 H3 H4. rewrite Id.Eval; try assumption.
  rewrite Id.Eval; assumption.
Qed.

(* The composition of two strictly monotone ordinal functions is monotone.      *)
Proposition Compose : forall (f g a b c:U),
  Ordinal a             ->
  Ordinal b             ->
  Ordinal c             ->
  Fun f a b             ->
  Fun g b c             ->
  Monotone f            ->
  Monotone g            ->
  Monotone (g :.: f).
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros f g a b c H1 H2 H3 H4 H5 H6 H7.
  assert (Fun (g :.: f) a c) as H8. { apply Fun.Compose with b; assumption. }
  apply FromFun with a c; try assumption.
  intros x y H9 H10 H11.
  (* Strict increase is preserved first by f and then by g.                     *)
  rewrite Fun.ComposeEval with f g a b c x; try assumption.
  rewrite Fun.ComposeEval with f g a b c y; try assumption.
  apply H7.
  - assert (domain g = b) as H12. { apply H5. }
    rewrite H12. apply Fun.IsInRange with a; assumption.
  - assert (domain g = b) as H12. { apply H5. }
    rewrite H12. apply Fun.IsInRange with a; assumption.
  - assert (domain f = a) as H12. { apply H4. }
    assert (x :< domain f) as H13. { rewrite H12. assumption. }
    assert (y :< domain f) as H14. { rewrite H12. assumption. }
    apply H6; assumption.
Qed.

(* There is a monotone function from succ a to succ b sending a to b.           *)
Proposition HasSuccFun : forall (a b:U),
  Ordinal a -> Ordinal b -> a :<=: b -> exists f,
    Monotone f /\ Fun f (succ a) (succ b) /\ f!a = b.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a b H1 H2 H3.
  remember (SFI.ifThenElse (succ a) (fun x => x :< a)
    (fun x => x) (fun _ => b)) as f eqn:H4.
  exists f.
  assert (Ordinal (succ a)) as H5. { apply Succ.IsOrdinal. assumption. }
  assert (Ordinal (succ b)) as H6. { apply Succ.IsOrdinal. assumption. }
  assert (Fun f (succ a) (succ b)) as H7. {
    rewrite H4. apply SFI.IsFun. split.
    - (* Points below a remain below succ b.                                    *)
      intros x H7 H8. apply Succ.Charac. right. apply H3. assumption.
    - (* The remaining point is sent to the top of succ b.                      *)
      intros x H7 H8. apply Succ.IsIn. }
  assert (Monotone f) as H8. {
    apply FromFun with (succ a) (succ b); try assumption.
    (* The piecewise function strictly preserves the order on succ a.           *)
    intros x y H8 H9 H10.
    apply Succ.Charac in H9. destruct H9 as [H9|H9].
    - (* If y is the top point a, the value of y is b.                          *)
      subst y.
      assert (x :< a) as H9. { assumption. }
      assert (~ a :< a) as H11. { apply Foundation.NoLoop1. }
      assert (f!x = x) as H12. { rewrite H4. apply SFI.Eval1; assumption. }
      assert (f!a = b) as H13. {
        rewrite H4. apply SFI.Eval2. 1: apply Succ.IsIn. assumption. }
      rewrite H12, H13.
      apply H3. assumption.
    - (* If y is below a, then x is also below a and both values are unchanged. *)
      assert (Ordinal y) as H11. { apply Core.IsOrdinal with a; assumption. }
      assert (Ordinal x) as H12. { apply Core.IsOrdinal with y; assumption. }
      assert (x :< a) as H13. { apply Core.ElemElemTran with y; assumption. }
      assert (f!x = x) as H14. { rewrite H4. apply SFI.Eval1; assumption. }
      assert (f!y = y) as H15. {
        rewrite H4. apply SFI.Eval1. 2: assumption.
        apply Succ.Charac. right. assumption. }
      rewrite H14, H15.
      assumption. }
  split. 1: assumption. split. 1: assumption.
  rewrite H4. apply SFI.Eval2. 1: apply Succ.IsIn.
  apply Foundation.NoLoop1.
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
