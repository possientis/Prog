Require Import ZF.Class.Equiv.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.Order.Isom.
Require Import ZF.Class.Relation.Bij.
Require Import ZF.Class.Relation.Bijection.
Require Import ZF.Class.Relation.BijectionOn.
Require Import ZF.Class.Relation.Compose.
Require Import ZF.Class.Relation.Converse.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Fun.
Require Import ZF.Class.Relation.Function.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Class.Relation.FunctionOn.
Require Import ZF.Class.Relation.I.
Require Import ZF.Class.Relation.OneToOne.
Require Import ZF.Class.Relation.Range.
Require Import ZF.Class.Relation.Relation.
Require Import ZF.Class.Relation.Restrict.
Require Import ZF.Class.V.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.EvalOfClass.

(* I|A is the restriction of the identity class I to the class A.               *)
Proposition Charac : forall (A:Class) (x:U),
  (I:|:A) x <-> exists y, A y /\ x = :(y,y):.
Proof.
  intros A x. split; intros H1.
  - destruct H1 as [y [z [H1 [H2 H3]]]]. apply I.Charac2 in H3. subst.
    exists z. split. 1: assumption. reflexivity.
  - destruct H1 as [y [H1 H2]]. exists y. exists y.
    split. 1: assumption. split. 1: assumption. apply I.Charac2. reflexivity.
Qed.

Proposition Charac2 : forall (A:Class) (y z:U),
  (I:|:A) :(y,z): <-> A y /\ y = z.
Proof.
  intros A y z. split; intros H1.
  - apply Restrict.Charac2 in H1. destruct H1 as [H1 H2].
    apply I.Charac2 in H2. subst. split. 1: assumption. reflexivity.
  - destruct H1 as [H1 H2]. subst. apply Restrict.Charac2.
    split. 1: assumption. apply I.Charac2. reflexivity.
Qed.

(* I|A is a functional class.                                                   *)
Proposition IsFunctional : forall (A:Class), Functional (I:|:A).
Proof.
  intros A. apply Restrict.IsFunctional, I.IsFunctional.
Qed.

(* I|A is a relation class.                                                     *)
Proposition IsRelation : forall (A:Class), Relation (I:|:A).
Proof.
  intros A. apply Restrict.IsRelation.
Qed.

(* I|A is a function class.                                                     *)
Proposition IsFunction : forall (A:Class), Function (I:|:A).
Proof.
  intros A. split.
  - apply IsRelation.
  - apply IsFunctional.
Qed.

(* The converse of I|A is I|A itself.                                           *)
Proposition Converse : forall (A:Class),
  (I:|:A)^:-1: :~: (I:|:A).
Proof.
  intros A x. split; intros H1.
  - destruct H1 as [y [z [H1 H2]]].
    apply Charac2 in H2. destruct H2 as [H2 H3]. subst.
    apply Charac2. split. 1: assumption. reflexivity.
  - apply Charac in H1. destruct H1 as [y [H1 H2]]. subst.
    apply Converse.Charac2Rev, Charac2. split. 1: assumption. reflexivity.
Qed.

(* I|A is a one-to-one class.                                                   *)
Proposition IsOneToOne : forall (A:Class), OneToOne (I:|:A).
Proof.
  intros A. split.
  - apply IsFunctional.
  - apply Functional.EquivCompat with (I:|:A).
    + apply Equiv.Sym, Converse.
    + apply IsFunctional.
Qed.

(* I|A is a bijection class.                                                    *)
Proposition IsBijection : forall (A:Class), Bijection (I:|:A).
Proof.
  intros A. split.
  - apply Restrict.IsRelation.
  - apply IsOneToOne.
Qed.


(* The domain of I|A is A.                                                      *)
Proposition Domain : forall (A:Class), domain (I:|:A) :~: A.
Proof.
  intros A.
  apply Equiv.Tran with (A :/\: domain I). 1: apply Restrict.DomainOf.
  apply Equiv.Tran with (A :/\: V).
  - apply Inter2.EquivCompatR, I.Domain.
  - apply Inter2VR.
Qed.

(* The range of I|A is A.                                                       *)
Proposition Range : forall (A:Class), range (I:|:A) :~: A.
Proof.
  intros A y. split; intros H1.
  - destruct H1 as [x H1]. apply Charac2 in H1.
    destruct H1 as [H1 H2]. subst. assumption.
  - exists y. apply Charac2. split. 1: assumption. reflexivity.
Qed.

(* I|A is a function class defined on A.                                        *)
Proposition IsFunctionOn : forall (A:Class), FunctionOn (I:|:A) A.
Proof.
  split.
  - apply IsFunction.
  - apply Domain.
Qed.

(* I|A is a bijection class defined on A.                                       *)
Proposition IsBijectionOn : forall (A:Class), BijectionOn (I:|:A) A.
Proof.
  intros A. split.
  - apply IsBijection.
  - apply Domain.
Qed.

(* I|A is a bijection class from A to A.                                        *)
Proposition IsBij : forall (A:Class), Bij (I:|:A) A A.
Proof.
  intros A. split.
  - apply IsBijectionOn.
  - apply Range.
Qed.


(* If x lies in A, then the value of I|A at x is x.                             *)
Proposition Eval : forall (A:Class) (x:U),
  A x -> (I:|:A)!x = x.
Proof.
  intros A x H1. apply eq_trans with I!x.
  - apply Restrict.Eval. 2: assumption. apply I.IsFunctional.
  - apply I.Eval.
Qed.

Proposition EqualCharac : forall (F A:Class),
  FunctionOn F A              ->
  (forall x, A x -> F!x = x)  ->
  F :~: I:|:A.
Proof.
  intros F A H1 H2. apply FunctionOn.EqualCharac' with A. 1: assumption.
  - apply IsFunctionOn.
  - intros x H3. rewrite H2. 2: assumption. symmetry. apply Eval. assumption.
Qed.


(* I|A is an isomorphism class from A to A w.r to R (and R).                    *)
Proposition IsIsom : forall (R A:Class), Isom (I:|:A) R R A A.
Proof.
  intros R A. split.
  - apply IsBij.
  - intros x y H1 H2.
    assert ((I:|:A)!x = x) as H4. { apply Eval. assumption. }
    assert ((I:|:A)!y = y) as H5. { apply Eval. assumption. }
    split; intros H3.
    + rewrite H4, H5. assumption.
    + rewrite H4, H5 in H3. assumption.
Qed.

Proposition IsConverseFF : forall (F A B:Class), Bij F A B ->
  F^:-1: :.: F :~: (I:|:A).
Proof.
  intros F A B [[[H1 H2] H3] H4] u. split; intros H5.
  - destruct H5 as [x [y [z [H5 [H6 H7]]]]]. subst.
    apply Converse.Charac2 in H7.
    assert (x = z) as H8. {
      revert H7. revert H6. apply OneToOne.CharacL. assumption. }
    subst. apply Charac2. split. 2: reflexivity. apply H3.
    exists y. assumption.
  - apply Charac in H5. destruct H5 as [x [H5 H6]]. subst.
    apply Compose.Charac2. apply H3 in H5.
    destruct H5 as [y H5].
    exists y. split. 1: assumption. apply Converse.Charac2Rev. assumption.
Qed.

Proposition IsFConverseF : forall (F A B:Class), Bij F A B ->
  F :.: F^:-1: :~: (I:|:B).
Proof.
  intros F A B H1. assert (H2 := H1). destruct H2 as [[[H2 _] _] _].
  apply Equiv.Tran with ((F^:-1:)^:-1: :.: F^:-1:).
  - apply Compose.EquivCompatL, Equiv.Sym, Converse.IsIdempotent. assumption.
  - apply IsConverseFF with A. apply Bij.Converse. assumption.
Qed.

Proposition IdentityL : forall (F A B:Class), Fun F A B ->
  (I:|:B) :.: F :~: F.
Proof.
  intros F A B H1. intros u. split; intros H2.
  - destruct H2 as [x [y [z [H2 [H3 H4]]]]]. apply Charac2 in H4.
    destruct H4 as [H4 H5]. subst. assumption.
  - assert (exists x y, u = :(x,y):) as H3. { apply H1. assumption. }
    destruct H3 as [x [y H3]]. subst. exists x. exists y. exists y.
    split. 1: reflexivity. split. 1: assumption.
    apply Charac2. split. 2: reflexivity. apply H1. exists x. assumption.
Qed.

Proposition IdentityR : forall (F A B:Class), Fun F A B ->
  F :.: (I:|:A) :~: F.
Proof.
  intros F A B H1. intros u. split; intros H2.
  - destruct H2 as [x [y [z [H2 [H3 H4]]]]]. apply Charac2 in H3.
    destruct H3 as [H3 H5]. subst. assumption.
  - assert (exists x y, u = :(x,y):) as H3. { apply H1. assumption. }
    destruct H3 as [x [y H3]]. subst. exists x. exists x. exists y.
    split. 1: reflexivity. split. 2: assumption.
    apply Charac2. split. 2: reflexivity. apply H1. exists y. assumption.
Qed.

Proposition WhenIsConverseGF : forall (F G A B:Class),
  Bij F A B                 ->
  Bij G A B                 ->
  (G^:-1: :.: F) :~: I:|:A  ->
  F :~: G.
Proof.
  intros F G A B H1 H2 H3.
  apply Equiv.Tran with ((I:|:B) :.: F).
    1: { apply Equiv.Sym, IdentityL with A, Bij.IsFun. assumption. }
  apply Equiv.Tran with ((G :.: G^:-1:) :.: F).
    1: { apply Compose.EquivCompatL, Equiv.Sym, IsFConverseF with A. assumption. }
  apply Equiv.Tran with (G :.: (G^:-1: :.: F)).
    1: { apply Compose.Assoc. }
  apply Equiv.Tran with (G :.: (I:|:A)).
    1: { apply Compose.EquivCompatR. assumption. }
  apply IdentityR with B, Bij.IsFun. assumption.
Qed.

Proposition WhenIsGConverseF : forall (F G A B:Class),
  Bij F A B                 ->
  Bij G A B                 ->
  (G :.: F^:-1:) :~: I:|:B  ->
  F :~: G.
Proof.
  intros F G A B H1 H2 H3.
  apply Equiv.Tran with ((I:|:B) :.: F).
    1: { apply Equiv.Sym, IdentityL with A, Bij.IsFun. assumption. }
  apply Equiv.Tran with ((G :.: F^:-1:) :.: F).
    1: { apply Compose.EquivCompatL, Equiv.Sym. assumption. }
  apply Equiv.Tran with (G :.: (F^:-1: :.: F)).
    1: { apply Compose.Assoc. }
  apply Equiv.Tran with (G :.: (I:|:A)).
    1: { apply Compose.EquivCompatR, IsConverseFF with B. assumption. }
  apply IdentityR with B, Bij.IsFun. assumption.
Qed.

