Require Import ZF.Class.Equiv.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Limit.
Require Import ZF.Set.Ordinal.Recursion2OfClass.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.FunctionOn.
Require Import ZF.Set.UnionGen.

Module SOR2 := ZF.Set.Ordinal.Recursion2OfClass.

(* The recursion set associated with the sets f a b.                            *)
(* In other words, when b is an ordinal, the unique function g                  *)
(* defined on b by the equations:                                               *)
(* (i)    g(0)      = a                                                         *)
(* (ii)   g(succ c) = f(g(c))                                                   *)
(* (iii)  g(c)      = \/_{x :< c} g(x) , if c is a limit ordinal                *)
Definition recursion (f a b:U) : U := (SOR2.recursion (toClass f) a b).

(* The recursion set of f a b is a function defined on b, when b is an ordinal. *)
Proposition IsFunctionOn : forall (f a b:U), Ordinal b ->
  FunctionOn (recursion f a b) b.
Proof.
  intros f. apply SOR2.IsFunctionOn.
Qed.

(* The recursion set of f a b has initial value a.                              *)
Proposition WhenZero : forall (f a b:U),
  Ordinal b                   ->
  b <> :0:                    ->
  (recursion f a b)!:0: = a.
Proof.
  intros f. apply SOR2.WhenZero.
Qed.

(* The recursion set satisfies the equation g(succ c) = f(g(c)).                *)
Proposition WhenSucc : forall (f a b c:U),
  Ordinal b                                               ->
  succ c :< b                                             ->
  (recursion f a b)!(succ c)  = f!((recursion f a b)!c).
Proof.
  intros f. apply SOR2.WhenSucc.
Qed.

(* The recursion set satisfies the equation:                                    *)
(* g(c) = \/_{x :< c} g(x) when c is a limit ordinal.                           *)
Proposition WhenLimit : forall (f a b c:U),
  Ordinal b ->
  Limit c   ->
  c :< b    ->
  (recursion f a b)!c = :\/:_{c} (recursion f a b).
Proof.
  intros f. apply SOR2.WhenLimit.
Qed.

(* The recursion set of f a b is the unique function defined on b which         *)
(* satisfies the three equation (i), (ii) and (iii).                            *)
Proposition IsUnique : forall (f g a b:U),
  Ordinal b                                                       ->
  FunctionOn g b                                                  ->
  g!:0: = a                                                       ->    (* (i)  *)
  (forall c, Ordinal c -> succ c :< b -> g!(succ c) = f!(g!c))    ->    (* (ii) *)
  (forall c, Limit c -> c :< b -> g!c = :\/:_{c} g)               ->    (* (iii)*)
  g = recursion f a b.
Proof.
  intros f g a b. apply SOR2.IsUnique.
Qed.


