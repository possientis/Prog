Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.Monotone.
Require Import ZF.Class.Ordinal.OrdFun.
Require Import ZF.Class.Ordinal.Recursion2.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.FunctionOn.
Require Import ZF.Class.Relation.Range.
Require Import ZF.Set.Core.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Limit.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.Ordinal.Omega.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.UnionGenOfClass.

Module CRF := ZF.Class.Relation.Function.

(* F0 : On -> On is the successor function class.                               *)
Definition F0 : Class := fun x => exists (y z:U), x = :(y,succ y): /\ On y.

Proposition F0Charac2 : forall (y z:U),
  F0 :(y,z): <-> On y /\ z = succ y.
Proof.
  intros y z. split; intros H1.
  - destruct H1 as [y' [z' [H1 H2]]].
    apply OrdPair.WhenEqual in H1. destruct H1 as [H1 H3]. subst.
    split. 1: assumption. reflexivity.
  - destruct H1 as [H1 H2]. exists y. exists z. subst.
    split. 2: assumption. reflexivity.
Qed.

(* F0 is defined on the ordinals.                                               *)
Lemma F0Domain : domain F0 :~: On.
Proof.
  intros y. split; intros H1.
  - destruct H1 as [z H1]. apply F0Charac2 in H1. apply H1.
  - exists (succ y). exists y. exists (succ y). split. 2: assumption. reflexivity.
Qed.

(* F0 is an ordinal function.                                                   *)
Lemma F0OrdFun : OrdFun F0.
Proof.
  split.
  - split.
    + intros x H1. destruct H1 as [y [z [H1 H2]]].
      exists y. exists (succ y). assumption.
    + intros x y z H1 H2. apply F0Charac2 in H1. apply F0Charac2 in H2.
      destruct H1 as [H1 H3]. destruct H2 as [H2 H4]. subst. reflexivity.
  - split.
    + apply Core.EquivCompat with On. 2: apply Core.OnIsOrdinal.
      apply Equiv.Sym, F0Domain.
    + intros z H1. destruct H1 as [y H1]. apply F0Charac2 in H1.
      destruct H1 as [H1 H2]. subst. apply Succ.IsOrdinal. assumption.
Qed.

(* F0 is the successor function on the class of ordinals.                       *)
Lemma F0Eval : forall (a:U), On a  -> F0!a = succ a.
Proof.
  intros a H1. apply CRF.EvalCharac.
  - apply F0OrdFun.
  - apply F0Domain. assumption.
  - apply F0Charac2. split. 1: assumption. reflexivity.
Qed.

(* F0 is a strictly increasing ordinal function.                                *)
Lemma F0Monotone : Monotone F0.
Proof.
  split. 1: apply F0OrdFun.
  intros a b H1 H2 H3. apply F0Domain in H1. apply F0Domain in H2.
  rewrite F0Eval, F0Eval; try assumption. apply Succ.ElemCompat; assumption.
Qed.

(* F : On -> On is defined recursively by:                                      *)
(* (i)    F(0) = 1                                                              *)
(* (ii)   F(a + 1) = F(a) + 1                                                   *)
(* (iii)  F(a) = \/{b :< a} F(b)  when a is a limit ordinal.                    *)
Definition F : Class := Recursion F0 :1:.

(* F is an ordinal function.                                                    *)
Lemma FOrdFun: OrdFun F.
Proof.
   apply OrdFun.FromRecursion.
   - apply OneIsOrdinal.
   - apply F0OrdFun.
   - apply F0Domain.
Qed.

(* F is defined on the class of ordinals.                                       *)
Lemma FDomain : domain F :~: On.
Proof.
  apply Recursion2.IsFunctionOn.
Qed.

(* F(0) = 1.                                                                    *)
Lemma FWhenZero : F!:0: = :1:.
Proof.
  unfold F. rewrite Recursion2.WhenZero. reflexivity.
Qed.

(* F(a + 1) = F(a) + 1.                                                         *)
Lemma FWhenSucc : forall (a:U),
  On a -> F!(succ a) = succ (F!a).
Proof.
  intros a H1. unfold F. rewrite Recursion2.WhenSucc. 2: assumption.
  rewrite F0Eval. 1: reflexivity. apply FOrdFun. exists a.
  apply CRF.Satisfies.
  - apply FOrdFun.
  - apply FDomain. assumption.
Qed.

(* F(a) = \/_{b :< a} F(b) when a is a limit ordinal.                           *)
Lemma FWhenLimit : forall (a:U),
  Limit a -> F!a = :\/:_{a} F.
Proof.
  apply Recursion2.WhenLimit.
Qed.

(* F(n) = n + 1 for all n :< N.                                                 *)
Lemma Fn : forall (n:U), n :< :N -> F!n = succ n.
Proof.
  apply Omega.Induction.
  - apply FWhenZero.
  - intros n H1 H2.  rewrite FWhenSucc.
    + rewrite H2. reflexivity.
    + apply Omega.HasOrdinalElem. assumption.
Qed.

(* F(N) = N.                                                                    *)
Lemma FN : F!:N = :N.
Proof.
  unfold F. rewrite Recursion2.WhenLimit. 2: apply Omega.IsLimit.
  fold F. apply DoubleInclusion. split; intros y H1.
  - apply UnionGenOfClass.Charac in H1. destruct H1 as [n [H1 H2]].
    assert (On (succ n)) as H3. {
      apply Omega.HasOrdinalElem. apply Omega.HasSucc. assumption. }
    rewrite Fn in H2. 2: assumption. apply SOC.ElemElemTran with (succ n);
    try assumption.
    + apply SOC.IsOrdinal with (succ n); assumption.
    + apply Omega.IsOrdinal.
    + apply Omega.HasSucc. assumption.
  - apply Limit.InBetween in H1. 2: apply Omega.IsLimit.
    destruct H1 as [n [H1 H2]]. apply UnionGenOfClass.Charac.
    exists n. split. 1: assumption. rewrite Fn. 2: assumption.
    assert (On n) as H3. { apply Omega.HasOrdinalElem. assumption. }
    apply SOC.ElemInclTran with n; try assumption.
    + apply SOC.IsOrdinal with n; assumption.
    + apply Succ.IsOrdinal. assumption.
    + apply Succ.IsIncl.
Qed.

(* F is a strictly increasing ordinal function.                                 *)
Lemma FMonotone : Monotone F.
Proof.
  unfold F. apply Monotone.FromRecursion.
  - apply OneIsOrdinal.
  - intros b H1. rewrite F0Eval. 2: assumption. apply IsIn.
  - apply F0Monotone.
  - apply F0Domain.
Qed.

(* We now define G by recursion from F and 0, namely with                       *)
(*  (i)   G(0) = 0                                                              *)
(*  (ii)  G(a + 1) = F(G(a))                                                    *)
(*  (iii) G(a) = \/_{b :< a} G(b) when a is a limit ordinal.                    *)
(* 0 is an ordinal and F is monotone, yet G fails to be monotone.               *)
Definition G:Class := Recursion F :0:.

(* G is an ordinal function.                                                    *)
Lemma GOrdFun : OrdFun G.
Proof.
  apply OrdFun.FromRecursion.
  - apply ZeroIsOrdinal.
  - apply FOrdFun.
  - apply FDomain.
Qed.

(* G is defined on the class of ordinals.                                       *)
Lemma GDomain : domain G :~: On.
Proof.
  apply Recursion2.IsFunctionOn.
Qed.

(* G(0) = 0.                                                                    *)
Lemma GWhenZero : G!:0: = :0:.
Proof.
  unfold G. rewrite Recursion2.WhenZero. reflexivity.
Qed.

(* G(a + 1) = F(G(a)).                                                          *)
Lemma GWhenSucc : forall (a:U), On a -> G!(succ a) = F!(G!a).
Proof.
  intros a H1. unfold G. rewrite Recursion2.WhenSucc. 2: assumption.
  reflexivity.
Qed.

(* G(a) = \/{b :< a} G(b) when a is a limit ordinal.                            *)
Lemma GWhenLimt : forall (a:U),
  Limit a -> G!a = :\/:_{a} G.
Proof.
  intros a H1. unfold G. rewrite Recursion2.WhenLimit. 2: assumption.
  reflexivity.
Qed.

(* G(n) = n for all n :< N.                                                     *)
Lemma Gn : forall (n:U), n :< :N -> G!n = n.
Proof.
  apply Omega.Induction.
  - apply GWhenZero.
  - intros b H1 H2. rewrite GWhenSucc.
    + rewrite H2, Fn. 2: assumption. reflexivity.
    + apply Omega.HasOrdinalElem. assumption.
Qed.

(* G(N) = N.                                                                    *)
Lemma GN : G!:N = :N.
Proof.
  unfold G. rewrite Recursion2.WhenLimit. 2: apply Omega.IsLimit.
  fold G. apply DoubleInclusion. split; intros y H1.
  - apply UnionGenOfClass.Charac in H1. destruct H1 as [n [H1 H2]].
    assert (On n) as H3. { apply Omega.HasOrdinalElem. assumption. }
    rewrite Gn in H2. 2: assumption. apply SOC.ElemElemTran with n;
    try assumption.
    + apply SOC.IsOrdinal with n; assumption.
    + apply Omega.IsOrdinal.
  - apply Limit.InBetween in H1. 2: apply Omega.IsLimit.
    destruct H1 as [n [H1 H2]]. apply UnionGenOfClass.Charac.
    exists n. split. 1: assumption. rewrite Gn; assumption.
Qed.

(* N :< succ N but  G(N) = G(succ N). So G is not strictly increasing.          *)
Lemma GSuccN : G!:N = G!(succ :N).
Proof.
  rewrite GN, GWhenSucc. 2: apply Omega.IsOrdinal. rewrite GN, FN. reflexivity.
Qed.

Lemma GNotMonotone : ~ Monotone G.
Proof.
  intros [_ H1]. specialize (H1 :N (succ :N)).
  assert (G!:N :< G!(succ :N)) as H2. {
    apply H1.
    - apply GDomain, Omega.IsOrdinal.
    - apply GDomain, Succ.IsOrdinal, Omega.IsOrdinal.
    - apply Succ.IsIn. }
  rewrite <- GSuccN in H2. apply Foundation.NoElemLoop1 with G!:N. assumption.
Qed.
