Require Import ZF.Class.Equiv.
Require Import ZF.Class.Order.Transport.
Require Import ZF.Class.Relation.Bij.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.EvalOfClass.

(* Predicate expressing the fact that R is an irreflexive class on A.           *)
Definition Irreflexive (R A:Class) : Prop := forall (x:U), A x -> ~ R :(x,x):.

(* Irreflexivity is preserved under transport by a bijection.                   *)
Proposition Transport : forall (F R S A B:Class),
  (S = transport F R A) -> Bij F A B -> Irreflexive R A -> Irreflexive S B.
Proof.
  (* Proof by Claude.                                                           *)
  intros F R S A B H1 H2 H3 y H4 H5.
  apply (Bij.RangeCharac F A B) in H4. 2: assumption.
  destruct H4 as [a [H4 H6]].
  rewrite <- H6 in H5. rewrite H1 in H5.
  apply (Transport.Charac2F F R A B a a H2 H4 H4) in H5.
  destruct H5 as [_ [_ H5]].
  revert H5. apply H3. assumption.
Qed.
