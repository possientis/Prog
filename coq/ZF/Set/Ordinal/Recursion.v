Require Import ZF.Class.Equiv.
Require Import ZF.Set.Core.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.RecursionOfClass.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.FunctionOn.
Require Import ZF.Set.Relation.Restrict.

Module SOR := ZF.Set.Ordinal.RecursionOfClass.

(* The recursion set associated with the sets f and a.                          *)
(* In other words, when a is an ordinal, the unique function g                  *)
(* defined on a by the recursion: forall b :< a, g(b) = f(g|b).                 *)
Definition recursion (f a:U) : U := SOR.recursion (toClass f) a.

(* Low level characterisation.                                                  *)
Proposition Charac : forall (f a x:U),
  x :< recursion f a                     <->
  exists y z g b,
    x = :(y,z):                           /\
    y :< a                                /\
    :(y,z): :< g                          /\
    Ordinal b                             /\
    FunctionOn g b                        /\
    (forall c, c :< b -> g!c = f!(g:|:c)).
Proof.
  intros f. apply SOR.Charac.
Qed.

Proposition Charac2 : forall (f a y z:U),
  :(y,z):  :< recursion f a              <->
  exists g b,
    y :< a                                /\
    :(y,z): :< g                          /\
    Ordinal b                             /\
    FunctionOn g b                        /\
    (forall c, c :< b -> g!c = f!(g:|:c)).
Proof.
  intros f. apply SOR.Charac2.
Qed.

(* The recursion set of f and a is a function defined on a, when a ordinal.     *)
Proposition IsFunctionOn : forall (f a:U), Ordinal a ->
  FunctionOn (recursion f a) a.
Proof.
  intros f. apply SOR.IsFunctionOn.
Qed.

(* The recursion set of f and a is f-recursive, when a is an ordinal.           *)
Proposition IsRecursive : forall (f a:U), Ordinal a ->
  forall b, b :< a -> (recursion f a)!b = f!((recursion f a) :|: b).
Proof.
  intros f. apply SOR.IsRecursive.
Qed.

(* The recursion set is the unique f-recursive function defined on a.           *)
Proposition IsUnique : forall (f g a:U),
  Ordinal a                             ->
  FunctionOn g a                        ->
  (forall b, b :< a -> g!b = f!(g:|:b)) ->
  g = recursion f a.
Proof.
  intros f g a. apply SOR.IsUnique.
Qed.
