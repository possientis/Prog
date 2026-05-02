Require Import ZF.Class.Equiv.
Require Import ZF.Class.Order.Transport.
Require Import ZF.Class.Relation.Bij.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.EvalOfClass.

(* Predicate expressing the fact that R is an anti-symmetric class on A.        *)
Definition AntiSymmetric (R A:Class) : Prop := forall (x y:U), A x -> A y ->
  R :(x,y): -> R :(y,x): -> x = y.

(* Anti-symmetry is preserved under transport by a bijection.                   *)
Proposition Transport : forall (F R S A B:Class),
  (S = transport F R A) -> Bij F A B -> AntiSymmetric R A -> AntiSymmetric S B.
Proof.
  (* Proof by Claude.                                                           *)
  intros F R S A B H1 H2 H3 y1 y2 H4 H5 H6 H7.
  apply (Bij.RangeCharac F A B) in H4. 2: assumption.
  apply (Bij.RangeCharac F A B) in H5. 2: assumption.
  destruct H4 as [a [H4 H8]]. destruct H5 as [b [H5 H9]].
  rewrite <- H8, <- H9 in H6. rewrite H1 in H6.
  rewrite <- H9, <- H8 in H7. rewrite H1 in H7.
  apply (Transport.Charac2F F R A B) in H6; try assumption.
  apply (Transport.Charac2F F R A B) in H7; try assumption.
  assert (a = b) as H10. { apply H3; assumption. }
  rewrite <- H8, <- H9. rewrite H10. reflexivity.
Qed.
