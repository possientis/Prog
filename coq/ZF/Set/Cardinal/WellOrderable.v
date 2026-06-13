Require Import ZF.Axiom.Choice.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Ordinal.Recursion.
Require Import ZF.Class.Relation.Fun.From.
Require Import ZF.Class.Small.
Require Import ZF.Set.Cardinal.Equiv.
Require Import ZF.Set.Core.
Require Import ZF.Set.Diff.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Limit.
Require Import ZF.Set.Ordinal.Mult.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.Ordinal.Omega.
Require Import ZF.Set.Ordinal.Plus.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Power.
Require Import ZF.Set.Prod.
Require Import ZF.Set.Relation.Bij.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Range.
Require Import ZF.Set.Relation.RestrictOfClass.
Require Import ZF.Set.Sum.

Require Import ZF.Notation.Eval.
Require Import ZF.Notation.Image.

Module CEQ := ZF.Class.Equiv.
Module CFO := ZF.Class.Relation.FunctionOn.
Module COF := ZF.Class.Ordinal.FunctionOn.
Module CFF := ZF.Class.Relation.Fun.From.
Module CRD := ZF.Class.Relation.Domain.
Module SCE := ZF.Set.Cardinal.Equiv.
Module SOC := ZF.Set.Ordinal.Core.
Module SRO := ZF.Set.Relation.OneToOne.
Module SRR := ZF.Set.Relation.RestrictOfClass.

(* A set is well-orderable iff it is equipotent to some ordinal.                *)
Definition WellOrderable (a:U) : Prop := exists (b:U), Ordinal b /\ a :~: b.

(* Every ordinal is well-orderable.                                             *)
Proposition WhenOrdinal : forall (a:U),
  Ordinal a -> WellOrderable a.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a H1.
  (* The ordinal itself is an ordinal representative of its cardinality.        *)
  exists a. split. 1: assumption. apply SCE.Refl.
Qed.

(* Assuming choice, every set is well-orderable.                                *)
Proposition WithChoice : Choice ->
  forall (a:U), WellOrderable a.
Proof.
  intros AC a. specialize (AC :P(a)). destruct AC as [f [H1 H2]].
  remember (fun x => f!(a :\: range x)) as G eqn:H3.
  remember (Recursion (CFF.from G)) as F eqn:H4.
  assert (forall x,
    a :\: range x <> :0: -> f!(a :\: range x) :< a :\: range x) as H5. {
      intros x H5. apply H2. 2: assumption.
      apply Power.Charac, Diff.IsIncl. }
  assert (forall b, Ordinal b -> F!b = :[G]:!(F:|:b)) as H6. {
    intros b H6. rewrite H4. apply Recursion.IsRecursive. assumption. }
  assert (forall b , Ordinal b ->
    a :\: range (F:|:b) <> :0: -> F!b :< a :\: range (F:|:b)) as H7. {
      intros b H7 H8. rewrite H6, CFF.Eval, H3. 2: assumption.
      apply H5. assumption. }
  assert (CFO.FunctionOn F Ordinal) as G1. {
    rewrite H4. apply Recursion.IsFunctionOn. }
  assert (Small (toClass a)) as G2. { apply Small.SetIsSmall. }
  assert (CRD.domain F :~: Ordinal) as G3. { apply G1. }
  assert (forall b, Ordinal b               ->
    (toClass a :\: F:[b]:) :<>: :0: ->
    (toClass a :\: F:[b]:) F!b) as H8. {
      intros b H8 H9.
      assert (range (F:|:b) = F:[b]:) as H10. {
        apply RestrictOfClass.RangeOf, G1. }
      apply Diff.ToClass. rewrite <- H10. apply H7. 1: assumption.
      intros H11. apply H9.
      apply CEQ.Tran with (toClass (a :\: range (F:|:b))).
      - apply CEQ.Sym. rewrite <- H10. apply Diff.ToClass.
      - apply Empty.EmptyToClass. assumption. }
  assert (exists b,
    Ordinal b                                                     /\
    (forall c, c :< b -> (toClass a :\: F:[c]:) :<>: :0:) /\
    toClass F:[b]: :~: toClass a                                  /\
    SRO.OneToOne (F:|:b)) as H9. { apply COF.WhenFreshAndSmall; assumption. }
  destruct H9 as [b [H9 [H10 [H11 H12]]]].
  assert (F:[b]: = a) as H13. { apply CEQ.EqualToClass. assumption. }
  assert (range (F:|:b) = a) as H14. {
    rewrite <- H13. apply RestrictOfClass.RangeOf, G1. }
  assert (domain (F:|:b) = b) as H15. {
    apply RestrictOfClass.DomainWhenIncl.
    - apply G1.
    - intros c H15. apply G3. apply SOC.IsOrdinal with b; assumption. }
  assert (Bij (F:|:b) b a) as H16. {
    split. 2: assumption. split. 2: assumption. split. 2: assumption.
    apply SRR.IsRelation, G1. }
  exists b. split. 1: assumption. apply SCE.Sym. exists (F:|:b). assumption.
Qed.

(* Being well-orderable is preserved by inclusion.                              *)
Proposition InclCompat : forall (a b:U),
  a :<=: b -> WellOrderable b -> WellOrderable a.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b H1 [c [H2 H3]].
  destruct H3 as [f H3].
  (* The image of a under the bijection b -> c is a subset of the ordinal c.    *)
  assert (f:[a]: :<=: c) as H4. {
    intros y H4. apply (Bij.ImageCharac f b c) in H4. 2: assumption.
    destruct H4 as [x [H4 [H5 H6]]].
    apply (Bij.RangeCharac f b c). 1: assumption. exists x. split; assumption. }
  (* That image has an ordinal representative inside c.                         *)
  assert (exists d, Ordinal d /\ d :<=: c /\ f:[a]: :~: d) as H5. {
    apply SCE.OrdinalSubset; assumption. }
  destruct H5 as [d [H5 [_ H6]]].
  (* Restricting the bijection to a bijects a with that image.                  *)
  assert (a :~: f:[a]:) as H7. {
    exists (f:|:a). apply (Bij.Restrict f b c); assumption. }
  exists d. split. 1: assumption. apply SCE.Tran with f:[a]:; assumption.
Qed.

(* The cartesian product of two well-orderable sets is well-orderable.          *)
Proposition Prod : forall (a b:U),
  WellOrderable a -> WellOrderable b -> WellOrderable (a :x: b).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b [c [H1 H2]] [d [H3 H4]].
  (* Replace both factors by ordinals, preserving the cartesian product.        *)
  assert (a :x: b :~: c :x: d) as H5. { apply SCE.CompatProd; assumption. }
  (* The ordinal product orders d x c as the ordinal d*c.                       *)
  assert (c :x: d :~: d :*: c) as H6. {
    exists (Mult2.f d c). apply Mult2.IsBij; assumption. }
  (* Transporting the bijections gives an ordinal representative.               *)
  exists (d :*: c). split.
  - apply Mult.IsOrdinal; assumption.
  - apply SCE.Tran with (c :x: d); assumption.
Qed.


(* The disjoint sum of two well-orderable sets is well-orderable.               *)
Proposition Sum : forall (a b:U),
  WellOrderable a -> WellOrderable b -> WellOrderable (a :++: b).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b [c [H1 H2]] [d [H3 H4]].
  (* Replace both summands by ordinals, preserving the disjoint sum.            *)
  assert (a :++: b :~: c :++: d) as H5. { apply SCE.SumCompat; assumption. }
  (* The ordinal sum orders c ++ d as the ordinal c+d.                          *)
  assert (c :++: d :~: c :+: d) as H6. {
    exists (Plus2.f c d). apply Plus2.IsBij; assumption. }
  (* Transporting the bijections gives an ordinal representative.               *)
  exists (c :+: d). split.
  - apply Plus.IsOrdinal; assumption.
  - apply SCE.Tran with (c :++: d); assumption.
Qed.


(* The successor of a well-orderable set is well-orderable.                     *)
Proposition Succ : forall (a:U),
  WellOrderable a -> WellOrderable (succ a).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a [b [H1 H2]].
  assert (succ a :~: succ b) as H3. { apply SCE.SuccCompat. assumption. }
  assert (Ordinal (succ b)) as H4. { apply Succ.IsOrdinal. assumption. }
  exists (succ b). split; assumption.
Qed.

(* A set is well-orderable when its successor is well-orderable.                *)
Proposition SuccRev : forall (a:U),
  WellOrderable (succ a) -> WellOrderable a.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a [c [H1 H2]].
  assert (c = :0: \/ Successor c \/ Limit c) as [H3|[H3|H3]]. {
    apply Limit.ThreeWay. assumption. }
  - exfalso. subst.
    assert (succ a = :0:) as H4. { apply SCE.WhenZero. assumption. }
    revert H4. apply Succ.NotZero.
  - destruct H3 as [b [H5 H4]]. subst.
    assert (a :~: b) as H6. { apply SCE.SuccCompatRev. assumption. }
    exists b. split; assumption.
  - assert (Ordinal c) as H4. { apply H3. }
    assert (:N :<=: c) as H5. { apply Omega.IsInclLimit. assumption. }
    assert (c :~: succ c) as H6. { apply SCE.Succ; assumption. }
    assert (succ a :~: succ c) as H7. { apply SCE.Tran with c; assumption. }
    assert (a :~: c) as H8. { apply SCE.SuccCompatRev. assumption. }
    exists c. split; assumption.
Qed.
