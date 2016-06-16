Require Import Relations.

Module Type DEC_ORDER.
  Parameter A : Set.
  Parameter le : A -> A -> Prop.
  Parameter lt : A -> A -> Prop.

  Axiom ordered : order A le.
  Axiom lt_le_weak : forall a b:A, lt a b ->  le a b.
  Axiom lt_diff : forall a b:A, lt a b -> a <> b.
  Axiom le_lt_or_eq : forall a b:A, le a b -> lt a b \/ a = b.
  Parameter lt_eq_lt_dec :
    forall a b:A, {lt a b}+{a = b}+{lt b a}.
End DEC_ORDER.

Print order.
(*
Record order (A : Type) (R : relation A) : Prop := Build_order
  { ord_refl : reflexive A R;
    ord_trans : transitive A R;
    ord_antisym : antisymmetric A R }
*)


Check Build_order.
(*
Build_order
     : forall (A : Type) (R : relation A),
       reflexive A R -> transitive A R -> antisymmetric A R -> order A R
*)


Module Type MORE_DEC_ORDERS.
  Parameter A : Set.
  Parameter le: A -> A -> Prop.
  Parameter lt: A -> A -> Prop.

  Axiom le_trans: transitive A le.
  Axiom le_refl: reflexive A le.
  Axiom le_antisym: antisymmetric A le.
  Axiom lt_irreflexive: forall a:A, ~lt a a.
  Axiom lt_trans: transitive A lt.
  Axiom lt_not_le: forall a b:A, lt a b -> ~le b a.
  Axiom le_not_lt: forall a b:A, le a b -> ~lt b a.
  Axiom lt_intro: forall a b:A, le a b -> a <> b -> lt a b.

  Parameter le_lt_dec: forall a b:A, {le a b}+{lt b a}.
  Parameter le_lt_eq_dec: forall a b:A, le a b -> {lt a b}+{a = b}.
End MORE_DEC_ORDERS.

(* Writing a functor between DEC_ORDER and MORE_DEC_ORDERS *)
Module More_Dec_Orders (P:DEC_ORDER) :
                        MORE_DEC_ORDERS
                        with Definition A := P.A
                        with Definition le := P.le
                        with Definition lt := P.lt.

  Definition A := P.A.
  Definition le := P.le.
  Definition lt := P.lt.

  (* low level proof *)
  Theorem le_trans : transitive A le.
  Proof.
    generalize P.ordered. intro H. elim H.
      clear H. intros. simpl. unfold A, le. assumption.
  Qed.

  (* high level proof *)
  Theorem le_refl: reflexive A le.
  Proof.
    case P.ordered. intros. auto.
  Qed.

  Theorem le_antisym: antisymmetric A le.
  Proof.
    case P.ordered. intros. auto.
  Qed.

  Theorem lt_intro: forall a b:A, le a b -> a <> b -> lt a b.
  Proof.
    intros a b H diff. generalize (P.le_lt_or_eq a b H). intro H0. elim H0.
      clear H0. intro H0. unfold lt. exact H0.
      clear H0. intro H0. apply False_ind, diff. exact H0.
  Qed.

  Theorem lt_irreflexive: forall a:A, ~lt a a.
  Proof.
    intros a H. generalize (P.lt_diff a a H). intro H0. apply H0. reflexivity.
  Qed.

  Theorem lt_not_le: forall a b:A, lt a b -> ~le b a.
  Proof.
    intros a b H0 H1.













