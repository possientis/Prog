Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.Oracle.
Require Import ZF.Class.Ordinal.Recursion.
Require Import ZF.Class.Relation.FunctionOn.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Limit.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.RestrictOfClass.
Require Import ZF.Set.UnionGenOfClass.

Module COR := ZF.Class.Ordinal.Recursion.

(* Transfinite recursion class associated with F and a. In other words, the     *)
(* unique function class G defined on On by the equations:                      *)
(* (i)    G(0)      = a                                                         *)
(* (ii)   G(succ b) = F(G(b))                                                   *)
(* (iii)  G(b)      = \/_{x :< b} G(x) , if b is a limit ordinal                *)
Definition Recursion (F:Class) (a:U) : Class := COR.Recursion (Oracle F a).

(* The transfinite recursion class is a function class defined on the ordinals. *)
Proposition IsFunctionOn : forall (F:Class) (a:U),
  FunctionOn (Recursion F a) On.
Proof.
  intros F a. apply COR.IsFunctionOn.
Qed.

(* The transfinite recursion class of F and a has initial value a.              *)
Proposition WhenZero : forall (F:Class) (a:U),
  (Recursion F a)!:0: = a.
Proof.
  intros F a. unfold Recursion. rewrite COR.IsRecursive.
  - apply Oracle.WhenZero.
  - apply ZeroIsOrdinal.
Qed.

(* The transfinite recursion class satisfies the equation G(succ b) = F(G(b)).  *)
Proposition WhenSucc : forall (F:Class) (a b:U), Ordinal b ->
  (Recursion F a)!(succ b) = F!((Recursion F a)!b).
Proof.
  intros F a b H1. unfold Recursion.
  assert (Ordinal (succ b)) as H2. { apply Succ.IsOrdinal. assumption. }
  rewrite COR.IsRecursive. 2: assumption.
  apply Oracle.WhenSucc. 1: assumption.
  - apply COR.IsFunction.
  - apply Incl.EquivCompatR with On.
    + apply Equiv.Sym, COR.DomainIsOn.
    + intros x H3. apply Core.IsOrdinal with (succ b); assumption.
Qed.

(* The transfinite recursion class satisfies the equation:                      *)
(* G(b) = \/_{x :< b} G(x) when b is a limit ordinal.                           *)
Proposition WhenLimit : forall (F:Class) (a b:U), Limit b ->
  (Recursion F a)!b = :\/:_{b} (Recursion F a).
Proof.
  intros F a b H1. unfold Recursion. rewrite COR.IsRecursive. 2: apply H1.
  apply Oracle.WhenLimit. 1: assumption.
  - apply COR.IsFunction.
  - apply Incl.EquivCompatR with On.
    + apply Equiv.Sym, COR.DomainIsOn.
    + intros x H2. apply Core.IsOrdinal with b. 2: assumption. apply H1.
Qed.

Proposition IsUnique : forall (F G:Class) (a:U),
  FunctionOn G On                               ->
  G!:0: = a                                     ->
  (forall b, Ordinal b -> G!(succ b) = F!(G!b)) ->
  (forall b, Limit b   -> G!b = :\/:_{b} G)     ->
  G :~: Recursion F a.
Proof.
Admitted.
