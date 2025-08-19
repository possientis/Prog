Require Import ZF.Class.Equiv.
Require Import ZF.Class.Ordinal.Induction.
Require Import ZF.Class.Ordinal.Recursion2.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Limit.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.FunctionOn.
Require Import ZF.Set.Relation.RestrictOfClass.
Require Import ZF.Set.Union.
Require Import ZF.Set.UnionGen.
Require Import ZF.Set.UnionGenOfClass.

(* The recursion set associated with the class F and sets a b.                  *)
(* In other words, when b is an ordinal, the unique function f                  *)
(* defined on b by the equations:                                               *)
(* (i)    f(0)      = a                                                         *)
(* (ii)   f(succ c) = F(f(c))                                                   *)
(* (iii)  f(c)      = \/_{x :< c} f(x) , if c is a limit ordinal                *)
Definition recursion (F:Class) (a b:U) : U := (Recursion F a) :|: b.

(* The recursion set of F and a b is a function defined on b, when b ordinal.   *)
Proposition IsFunctionOn : forall (F:Class) (a b:U), Ordinal b ->
  FunctionOn (recursion F a b) b.
Proof.
  apply Recursion2.RestrictIsFunctionOn.
Qed.

(* The recursion set of F and a b has initial value a.                          *)
Proposition WhenZero : forall (F:Class) (a b:U),
  Ordinal b                   ->
  b <> :0:                    ->
  (recursion F a b)!:0: = a.
Proof.
  intros F a b H1 H2. unfold recursion. rewrite RestrictOfClass.Eval.
  - apply Recursion2.WhenZero.
  - apply Recursion2.IsFunctionOn.
  - apply Core.HasZero; assumption.
Qed.

(* The recursion set satisfies the equation G(succ c) = F(G(c)).                *)
Proposition WhenSucc : forall (F:Class) (a b c:U),
  Ordinal b                                               ->
  succ c :< b                                             ->
  (recursion F a b)!(succ c)  = F!((recursion F a b)!c).
Proof.
  intros F a b c H1 H2. unfold recursion.
  assert (c :< b) as H3. {
    apply Core.ElemIsIncl in H2. 2: assumption. apply H2, Succ.IsIn. }
  assert (Ordinal c) as H4. {
    apply  Core.IsOrdinal with b; assumption. }
  rewrite RestrictOfClass.Eval, RestrictOfClass.Eval; try assumption.
  - apply Recursion2.WhenSucc. assumption.
  - apply Recursion2.IsFunctionOn.
  - apply Recursion2.IsFunctionOn.
Qed.

(* The recursion set satisfies the equation:                                    *)
(* G(c) = \/_{x :< c} G(x) when c is a limit ordinal.                           *)
Proposition WhenLimit : forall (F:Class) (a b c:U),
  Ordinal b ->
  Limit c   ->
  c :< b    ->
  (recursion F a b)!c = :\/:_{c} (recursion F a b).
Proof.
  intros F a b c H1 H2 H3.
  assert (:\/:_{c} (recursion F a b) = :\/:_{c} (Recursion F a)) as H4. {
    apply UnionGenOfClass.EqualCharac. intros x H4. unfold recursion.
    apply RestrictOfClass.Eval.
    - apply Recursion2.IsFunctionOn.
    - apply Core.ElemIsIncl in H3. 2: assumption. apply H3. assumption. }
  rewrite H4. unfold recursion. rewrite RestrictOfClass.Eval. 3: assumption.
  - apply Recursion2.WhenLimit. assumption.
  - apply Recursion2.IsFunctionOn.
Qed.

(* The recursion set of F a b is the unique function defined on b which         *)
(* satisfies the three equation (i), (ii) and (iii).                            *)
Proposition IsUnique : forall (F:Class) (a b f:U),
  Ordinal b                                                       ->
  FunctionOn f b                                                  ->
  f!:0: = a                                                       ->    (* (i)  *)
  (forall c, Ordinal c -> succ c :< b -> f!(succ c) = F!(f!c))    ->    (* (ii) *)
  (forall c, Limit c -> c :< b -> f!c = :\/:_{c} f)               ->    (* (iii)*)
  f = recursion F a b.
Proof.
  intros F a b f H1 H2 H3 H4 H5.
  apply FunctionOn.EqualCharac with b b. 1: assumption.
  - apply IsFunctionOn. assumption.
  - reflexivity.
  - intros c H6.
    assert (Ordinal c) as H7. { apply Core.IsOrdinal with b; assumption. }
    revert c H7 H6.
    remember (fun c => c :< b -> f!c = (recursion F a b)!c) as A eqn:H6.
    assert (forall c, Ordinal c -> A c) as H7. {
      apply Induction2.
      - rewrite H6. intros H7. rewrite H3. symmetry. apply WhenZero. 1: assumption.
        apply Empty.HasElem. exists :0:. assumption.
      - rewrite H6. intros c H7 H8 H9. rewrite H4; try assumption. rewrite H8.
        + symmetry. apply WhenSucc; assumption.
        + apply Core.ElemIsIncl in H9. 2: assumption. apply H9, Succ.IsIn.
      - rewrite H6. intros c H7 H8 H9. rewrite H5; try assumption. symmetry.
        assert (:\/:_{c} f = :\/:_{c} (recursion F a b)) as H10. {
          apply UnionGen.EqualCharac. intros x H11. apply H8. 1: assumption.
          apply Core.ElemIsIncl in H9. 2: assumption. apply H9. assumption. }
        rewrite H10. apply WhenLimit; assumption. }
    rewrite H6 in H7. assumption.
Qed.


