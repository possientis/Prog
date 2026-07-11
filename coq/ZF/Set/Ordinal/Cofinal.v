Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Limit.
Require Import ZF.Set.Ordinal.Monotone.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.Fun.

Require Import ZF.Notation.Eval.

Module SOM := ZF.Set.Ordinal.Monotone.


(* Predicate expressing the fact that a is cofinal with b.                      *)
Definition Cofinal (a b:U) : Prop :=
  b :<=: a                                              /\
  exists f,
    Monotone f                                          /\
    Fun f b a                                           /\
    forall c, c :< a -> exists d, d :< b /\ c :<=: f!d.

(* A set is cofinal with zero exactly when it is zero.                          *)
Proposition WhenZero : forall (a:U),
  Cofinal a :0: <-> a = :0:.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a. split; intros H1.
  - (* Any element of a would be bounded by a value indexed by zero.            *)
    apply Empty.WhenNoElem. intros c H2.
    destruct H1 as [_ [f [_ [_ H3]]]].
    assert (exists d, d :< :0: /\ c :<=: f!d) as H4. { apply H3. assumption. }
    destruct H4 as [d [H4 _]].
    apply Empty.NoElem in H4. contradiction.
  - (* For zero itself, the empty function witnesses cofinality vacuously.      *)
    subst. split.
    + apply Empty.IsIncl.
    + exists :0:.
      assert (Monotone :0:) as H1. { apply SOM.WhenZero. reflexivity. }
      assert (Fun :0: :0: :0:) as H2. { apply Fun.WhenZero. reflexivity. }
      split. 1: assumption. split. 1: assumption.
      intros c H3. exfalso. apply Empty.Charac in H3. contradiction.
Qed.

(* Successor ordinals are cofinal when the second is contained in the first.    *)
Proposition WhenSuccessor : forall (a b:U),
  Successor a   ->
  Successor b   ->
  b :<=: a      ->
  Cofinal a b.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a b H1 H2 H3.
  destruct H1 as [a' [H1 H4]]. destruct H2 as [b' [H2 H5]]. subst.
  assert (b' :<=: a') as H6. { apply Succ.InclCompatRev; assumption. }
  assert (exists f,
    Monotone f                /\
    Fun f (succ b') (succ a') /\
    f!b' = a') as H7. {
      apply SOM.HasSuccFun; assumption. }
  destruct H7 as [f [H7 [H8 H9]]]. split. 1: assumption.
  exists f. split. 1: assumption. split. 1: assumption.
  intros c H10.
  (* The top element of b maps to the top element of a, so it bounds c.         *)
  exists b'. split. 1: apply Succ.IsIn. rewrite H9.
  apply Succ.Charac in H10. destruct H10 as [H10|H10].
  - subst. apply Incl.Refl.
  - apply Core.ElemIsIncl; assumption.
Qed.

(* A successor ordinal containing one is cofinal with one.                      *)
Proposition WhenOne : forall (a:U),
  :1: :<=: a      ->
  Successor a     ->
  Cofinal a :1:.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a H1 H2.
  (* Since one is the successor of zero, the successor case applies directly.   *)
  apply WhenSuccessor; try assumption.
  apply Succ.IsSuccessor. apply Natural.Zero.
Qed.

(* Cofinal ordinals are limit ordinals together.                                *)
Proposition LimitCompat : forall (a b:U), Ordinal a -> Ordinal b ->
  Cofinal a b -> (Limit a <-> Limit b).
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a b H1 H2 H3. split; intros H4.
  - assert (Limit b) as H5. 2: assumption.
    (* If a is a limit, b cannot be zero or a successor.                        *)
    assert (b = :0: \/ Successor b \/ Limit b) as H6. {
      apply Limit.ThreeWay. assumption. }
    destruct H6 as [H6|[H6|H6]]. 3: assumption.
    + subst. apply WhenZero in H3. subst. exfalso.
      apply Limit.NotZero. assumption.
    + destruct H6 as [b' [H6 H7]]. subst.
      destruct H3 as [_ [f [H7 [H8 H9]]]].
      assert (f!b' :< a) as H10. {
        apply Fun.IsInRange with (succ b'); try assumption. apply Succ.IsIn. }
      assert (succ f!b' :< a) as H11. { apply Limit.HasSucc; assumption. }
      assert (exists d, d :< succ b' /\ succ f!b' :<=: f!d) as H12. {
        apply H9. assumption. }
      destruct H12 as [d [H12 H13]].
      assert (H14 := H12).
      assert (d :<=: b') as H15. {
        apply Succ.Charac in H12. destruct H12 as [H12|H12].
        - subst. apply Incl.Refl.
        - apply Core.ElemIsIncl; assumption. }
      assert (domain f = succ b') as H16. { apply H8. }
      assert (f!d :<=: f!b') as H17. {
        apply SOM.Relax; try assumption.
        - rewrite H16. assumption.
        - rewrite H16. apply Succ.IsIn.
      }
      assert (succ f!b' :<=: f!b') as H18. {
        apply Incl.Tran with (f!d); assumption. }
      exfalso. apply (Foundation.NoLoop1 (f!b')). apply H18. apply Succ.IsIn.
  - assert (Limit a) as H5. 2: assumption.
    (* If b is a limit, every element of a has its successor still below a.     *)
    destruct H3 as [H3 [f [H6 [H7 H8]]]].
    destruct H6 as [H6 G1].
    assert (a <> :0:) as H9. {
      (* Since a contains the nonzero limit b, a is not zero.                   *)
      assert (:0: :< b) as H9. { apply Limit.HasZero. assumption. }
      assert (:0: :< a) as H10. { apply H3. assumption. }
      intros H11. rewrite H11 in H10. apply Empty.Charac in H10. contradiction. }
    assert (forall c, c :< a -> succ c :< a) as H10. {
      (* Cofinality and monotonicity push each element below a larger value.    *)
      intros c H10.
      assert (exists d, d :< b /\ c :<=: f!d) as H11. { apply H8. assumption. }
      destruct H11 as [d [H11 H12]].
      assert (succ d :< b) as H13. { apply Limit.HasSucc; assumption. }
      assert (domain f = b) as H14. { apply H7. }
      assert (f!d :< f!(succ d)) as H15. {
        apply G1.
        - rewrite H14. assumption.
        - rewrite H14. assumption.
        - apply Succ.IsIn. }
      assert (f!(succ d) :< a) as H16. {
        apply Fun.IsInRange with b; assumption. }
      assert (Ordinal c) as H17. { apply Core.IsOrdinal with a; assumption. }
      assert (Ordinal f!d) as H18. {
        assert (f!d :< a) as G2. { apply Fun.IsInRange with b; assumption. }
        apply Core.IsOrdinal with a; assumption. }
      assert (Ordinal f!(succ d)) as H19. {
        apply Core.IsOrdinal with a; assumption. }
      assert (c :< f!(succ d)) as H20. {
        apply Core.InclElemTran with (f!d); assumption. }
      assert (succ c :<=: f!(succ d)) as H21. {
        apply Succ.ElemIsIncl; assumption. }
      apply Core.InclElemTran with (f!(succ d)); try assumption.
      apply Succ.IsOrdinal. assumption. }
    apply Limit.WhenHasSucc; assumption.
Qed.

