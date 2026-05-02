Require Import ZF.Class.Equiv.
Require Import ZF.Class.Order.Transport.
Require Import ZF.Class.Relation.Bij.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.EvalOfClass.

(* Predicate expressing the fact that R is a reflexive class on A.              *)
Definition Reflexive (R A:Class) : Prop := forall (x:U), A x -> R :(x,x):.

(* Reflexivity is preserved under transport by a bijection.                     *)
Proposition Transport : forall (F R S A B:Class),
  (S = transport F R A) -> Bij F A B -> Reflexive R A -> Reflexive S B.
Proof.
  (* Proof by Claude.                                                           *)
  intros F R S A B H1 H2 H3 y H4.
  apply (Bij.RangeCharac F A B) in H4. 2: assumption.
  destruct H4 as [a [H4 H5]].
  rewrite <- H5. rewrite H1.
  apply (Transport.Charac2F F R A B). 1-3: assumption. apply H3. assumption.
Qed.
