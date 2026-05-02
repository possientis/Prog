Require Import ZF.Class.Equiv.
Require Import ZF.Class.Order.Transport.
Require Import ZF.Class.Relation.Bij.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.EvalOfClass.

(* Predicate expressing the fact that R is a transitive class on A.             *)
Definition Transitive (R A:Class) : Prop := forall (x y z:U), A x -> A y -> A z ->
  R :(x,y): -> R :(y,z): -> R :(x,z):.

(* Transitivity is preserved under transport by a bijection.                    *)
Proposition Transport : forall (F R S A B:Class),
  (S = transport F R A) -> Bij F A B -> Transitive R A -> Transitive S B.
Proof.
  (* Proof by Claude.                                                           *)
  intros F R S A B H1 H2 H3 x y z H4 H5 H6 H7 H8.
  apply (Bij.RangeCharac F A B) in H4. 2: assumption.
  apply (Bij.RangeCharac F A B) in H5. 2: assumption.
  apply (Bij.RangeCharac F A B) in H6. 2: assumption.
  destruct H4 as [a [H4 Ha]]. destruct H5 as [b [H5 Hb]].
  destruct H6 as [c [H6 Hc]].
  rewrite <- Ha, <- Hb in H7. rewrite H1 in H7.
  rewrite <- Hb, <- Hc in H8. rewrite H1 in H8.
  apply (Transport.Charac2F F R A B) in H7. 2-4: assumption.
  apply (Transport.Charac2F F R A B) in H8. 2-4: assumption.
  rewrite <- Ha, <- Hc. rewrite H1.
  apply (Transport.Charac2F F R A B). 1-3: assumption. apply H3 with b; assumption.
Qed.

