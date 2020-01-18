Require Import Core.Set.
Require Import Core.Elem.
Require Import Core.Equal.
Require Import Core.Syntax.
Require Import Core.Semantics.
Require Import Core.Compatible.
Require Import Core.Environment.

(* Given an environement e, a variable n and a formula p, we can define a       *)
(* predicate P: set -> Prop by defining P x as the proposition obtained by      *)
(* evaluating the formula p in an environment where n is bound to x.            *)
Definition eval' (e:Env) (n:nat) (p:Formula) (x:set) : Prop :=
    eval (bind e n x) p.

(* Any predicate obtained by a formula is a compatible predicate.               *)
Theorem formulaCompatible : forall (e:Env) (n:nat) (p:Formula),
    compatible (eval' e n p). 
Proof.
    intros e n p. revert e n. induction p as [|k m|p1 IH1 p2 IH2|k p1 IH1];
    intros e n; unfold compatible, eval'; intros x y E; simpl; intros H.
    - assumption.
    -

Show.



