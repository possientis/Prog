Require Import ZF.Set.Core.
Require Import ZF.Class.Empty.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Incl.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Order.Isom.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Limit.
Require Import ZF.Set.Ordinal.Monotone.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.Ordinal.Order.
Require Import ZF.Set.Ordinal.Order.E.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Relation.Bij.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.Compose.
Require Import ZF.Set.Relation.Fun.
Require Import ZF.Set.Relation.Id.
Require Import ZF.Set.Relation.Image.
Require Import ZF.Set.Specify.
Require Import ZF.Set.Union.

Require Import ZF.Notation.Eval.

Module SOM := ZF.Set.Ordinal.Monotone.
Module SOO := ZF.Set.Ordinal.Order.
Module SOE := ZF.Set.Ordinal.Order.E.
Module CEM := ZF.Class.Empty.


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

(* A limit ordinal cofinal with b is the union of a function image of b.        *)
Proposition UnionImage : forall (a b:U),
  Limit a   ->
  Cofinal a b ->
  exists f, Fun f b a /\ a = :U(f:[b]:).
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a b H1 H2.
  (* Use the function that already witnesses the cofinality of a by b.          *)
  destruct H2 as [_ [f [_ [H2 H3]]]]. exists f. split. 1: assumption.
  assert (a :<=: :U(f:[b]:)) as H4. {
    (* Each element of a belongs to a value of the cofinal image.               *)
    intros c H4. apply Union.Charac.
    assert (succ c :< a) as H5. { apply Limit.HasSucc; assumption. }
    assert (exists d, d :< b /\ succ c :<=: f!d) as H6. {
      apply H3. assumption. }
    destruct H6 as [d [H6 H7]]. exists f!d. split.
    - apply H7. apply Succ.IsIn.
    - apply Image.Charac. exists d. split. 1: assumption.
      apply Fun.Satisfies with b a; assumption. }
  assert (:U(f:[b]:) :<=: a) as H5. {
    (* Conversely, every value in the image already lies below a.               *)
    intros c H5. apply Union.Charac in H5. destruct H5 as [d [H5 H6]].
    assert (f:[b]: :<=: a) as H7. {
      apply (Fun.ImageIncl f b a b); try assumption. apply Incl.Refl. }
    assert (d :< a) as H8. { apply H7. assumption. }
    assert (Ordinal a) as H9. { apply H1. }
    apply Core.Charac in H9. destruct H9 as [H9 _].
    apply H9 with d; assumption. }
  apply Incl.Double. split; assumption.
Qed.

(* Every ordinal is cofinal with itself.                                        *)
Proposition Refl : forall (a:U),
  Ordinal a -> Cofinal a a.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a H1.
  (* The identity on a is the cofinal map from a into itself.                   *)
  split. 1: apply Incl.Refl.
  exists (id a). split. 1: apply SOM.WhenId; assumption.
  split. 1: apply Id.IsFun.
  (* Each element of a is bounded by its own identity value.                    *)
  intros c H2. exists c. split. 1: assumption.
  rewrite Id.Eval; try assumption. apply Incl.Refl.
Qed.

(* Cofinality is transitive on ordinals.                                        *)
Proposition Tran : forall (a b c:U),
  Ordinal a     ->
  Ordinal b     ->
  Ordinal c     ->
  Cofinal a b   ->
  Cofinal b c   ->
  Cofinal a c.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a b c H1 H2 H3 H4 H5.
  destruct H4 as [H4 [f [H6 [H7 H8]]]].
  destruct H5 as [H5 [g [H9 [H10 H11]]]].
  (* The composed cofinal maps have source c and target a.                      *)
  assert (c :<=: a) as H12. { apply Incl.Tran with b; assumption. }
  split. 1: assumption.
  assert (Fun (f :.: g) c a) as H13. { apply Fun.Compose with b; assumption. }
  exists (f :.: g). split.
  - apply SOM.Compose with c b a; assumption.
  - split. 1: assumption.
    intros x H14.
    (* First bound x by a value of f, then bound that index by a value of g.    *)
    assert (exists y, y :< b /\ x :<=: f!y) as H15. { apply H8. assumption. }
    destruct H15 as [y [H15 H16]].
    assert (exists z, z :< c /\ y :<=: g!z) as H17. { apply H11. assumption. }
    destruct H17 as [z [H17 H18]]. exists z. split. 1: assumption.
    assert (f!y :<=: f!(g!z)) as H19. {
      apply SOM.Relax; try assumption.
      - assert (domain f = b) as H19. { apply H7. } rewrite H19. assumption.
      - assert (domain f = b) as H19. { apply H7. } rewrite H19.
        apply Fun.IsInRange with c; assumption. }
    assert (x :<=: f!(g!z)) as H20. { apply Incl.Tran with (f!y); assumption. }
    rewrite Fun.ComposeEval with g f c b a z; try assumption.
Qed.

(* A weakly cofinal map on b contains a cofinal monotone submap.                *)
Proposition Extract : forall (a b:U),
  Ordinal a                                               ->
  Ordinal b                                               ->
  b :<=: a                                                ->
  (exists f, Fun f b a /\
    forall c, c :< a -> exists d, d :< b /\ c :<=: f!d)   ->
  exists e, e :<=: b /\ Cofinal a e.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a b H1 H2 H3 H4.
  destruct H4 as [f [H4 H5]].
  (* The proof uses the indices where f strictly beats all earlier values.      *)
  (* This local set extracts the monotone cofinal subsequence.                  *)
  remember (fun d => forall x, x :< d -> f!x :< f!d) as A eqn:HA.
  remember {{ d :< b | A }} as r eqn:Hr.
  assert (r :<=: b) as H6. { rewrite Hr. apply Specify.IsInclL. }
  assert (exists e h, Ordinal e /\ e :<=: b /\ Isom h (E e) (E r) e r) as H7. {
    apply SOO.OrdinalSubset; assumption. }
  destruct H7 as [e [h [H7 [H8 H9]]]].
  assert (Bij h e r) as H10. { apply H9. }
  assert (Fun h e r) as H11. { apply Bij.IsFun. assumption. }
  assert (Fun h e b) as H12. { apply Fun.InclCompatR with r; assumption. }
  assert (Fun (f :.: h) e a) as H13. { apply Fun.Compose with b; assumption. }
  assert (Monotone (f :.: h)) as H14. {
    apply SOM.FromFun with e a; try assumption.
    intros x y H14 H15 H16.
    (* The isomorphism lists record indices in increasing order.                *)
    rewrite Fun.ComposeEval with h f e b a x; try assumption.
    rewrite Fun.ComposeEval with h f e b a y; try assumption.
    destruct H9 as [_ H9].
    assert (:( h!x , h!y ): :< E r) as H17. {
      apply H9; try assumption. apply SOE.Charac2. split. 1: assumption.
      split; assumption. }
    apply SOE.Charac2 in H17. destruct H17 as [H17 [H18 H19]].
    rewrite Hr in H18. apply Specify.Charac in H18.
    destruct H18 as [_ H18]. rewrite HA in H18. apply H18. assumption. }
  assert (forall c, c :< a -> exists d, d :< e /\ c :<=: (f :.: h)!d) as H15. {
    intros c H15.
    assert (Ordinal c) as H16. { apply Core.IsOrdinal with a; assumption. }
    (* First choose the least index whose f-value bounds c.                     *)
    remember (fun d => d :< b /\ c :<=: f!d) as B eqn:HB.
    assert (B :<=: Ordinal) as H17. {
      intros d H17. rewrite HB in H17. destruct H17 as [H17 _].
      apply Core.IsOrdinal with b; assumption. }
    assert (exists d, Ordinal d /\ B d /\ forall x, B x -> d :<=: x) as H18. {
      apply Core.HasMinimal. 1: assumption. apply CEM.HasElem.
      assert (exists d, d :< b /\ c :<=: f!d) as G1. { apply H5. assumption. }
      destruct G1 as [d G1]. exists d. rewrite HB. assumption. }
    destruct H18 as [d [H18 [H19 H20]]]. rewrite HB in H19.
    destruct H19 as [H19 H21].
    assert (f!d :< a) as G1. { apply Fun.IsInRange with b; assumption. }
    assert (Ordinal (f!d)) as G2. { apply Core.IsOrdinal with a; assumption. }
    assert (d :< r) as H22. {
      rewrite Hr. apply Specify.Charac. split. 1: assumption. rewrite HA.
      intros x H22.
      assert (Ordinal x) as G3. { apply Core.IsOrdinal with d; assumption. }
      assert (x :< b) as G4. { apply Core.ElemElemTran with d; assumption. }
      assert (f!x :< a) as G5. { apply Fun.IsInRange with b; assumption. }
      assert (Ordinal (f!x)) as G6. { apply Core.IsOrdinal with a; assumption. }
      (* Minimality says no earlier index already bounds c.                     *)
      assert (~ c :<=: f!x) as H23. {
        intros H23.
        assert (B x) as H24. { rewrite HB. split; assumption. }
        assert (d :<=: x) as H25. { apply H20. assumption. }
        assert (d :< d) as H26. {
          apply Core.InclElemTran with x; assumption. }
        apply Foundation.NoLoop1 with d. assumption. }
      assert (f!x :< c) as H24. {
        assert (f!x :< c \/ c :<=: f!x) as H25. {
          apply Core.ElemOrIncl; assumption. }
        destruct H25 as [H25|H25]. 1: assumption. contradiction. }
      apply Core.ElemInclTran with c; assumption. }
    assert (exists v, v :< e /\ h!v = d) as H23. {
      apply (Bij.RangeCharac h e r d). 1: assumption. assumption. }
    destruct H23 as [v [H23 H24]]. exists v. split. 1: assumption.
    rewrite Fun.ComposeEval with h f e b a v; try assumption. rewrite H24.
    assumption. }
  exists e. split. 1: assumption. split.
  - apply Incl.Tran with b; assumption.
  - exists (f :.: h). split. 1: assumption. split; assumption.
Qed.

