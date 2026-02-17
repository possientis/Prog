Require Import ZF.Class.Relation.ToFun.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Omega.
Require Import ZF.Set.Ordinal.RecursionNOfClass.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Ordinal.Transitive.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Union.
Require Import ZF.Set.Union2.
Require Import ZF.Set.UnionGen.

Require Import ZF.Notation.Eval.

Module SOR := ZF.Set.Ordinal.RecursionNOfClass.

(* Every set has a smallest transitive superset.                                *)
Proposition Exists : forall a, exists b,
  a :<=: b                                          /\
  Transitive b                                      /\
  (forall c, a :<=: c -> Transitive c -> b :<=: c).
Proof.
  intros a.
  remember (fun x => x :\/: :U(x)) as F eqn:H1.
  remember (SOR.recursion :[F]: a) as f eqn:H2.
  remember (:\/:_{:N} f) as b eqn:H3.
  exists b.
  assert (a = f!:0:) as H4. { rewrite H2, SOR.WhenZero. reflexivity. }
  assert (f!:0: :<=: b) as H5. {
    rewrite H3. apply UnionGen.IsIncl, Omega.HasZero. }
  assert (a :<=: b) as H6. { rewrite H4. assumption. }
  assert (forall n, n :< :N -> f!n :<=: f!(succ n)) as H7. {
    intros n H7. rewrite H2, SOR.WhenSucc, <- H2, ToFun.Eval, H1.
    2: assumption. apply Union2.IsInclL. }
  assert (forall n, n :< :N -> :U(f!n) :<=: f!(succ n)) as H8. {
    intros n H8. rewrite H2, SOR.WhenSucc, <- H2, ToFun.Eval, H1.
    2: assumption. apply Union2.IsInclR. }
Admitted.
