Require Import ZF.Class.Equiv.
Require Import ZF.Class.ProdGen.
Require Import ZF.Class.Relation.Fun.From.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.Fun.
Require Import ZF.Set.Relation.Functional.
Require Import ZF.Set.Relation.FunctionOn.
Require Import ZF.Set.Relation.Map.
Require Import ZF.Set.Relation.Restrict.
Require Import ZF.Set.Single.
Require Import ZF.Set.UnionGenOfClass.


Require Import ZF.Notation.ProdGen.
Export ZF.Notation.ProdGen.


(* The generalized product prd_{x :< a} A(x).                                   *)
Definition prodGen (a:U) (A:Class) : U := fromClass (Class.ProdGen.prodGen a A)
  (ProdGen.IsSmall A a).

(* Notation ":prd:_{ a } A" := (prodGen a A)                                    *)
Global Instance ProdGenOfClass : ProdGen U Class := { prodGen := prodGen }.

(* A set belongs to the product iff it is a function choosing from each fibre.  *)
Proposition Charac : forall (A:Class) (a f:U),
  f :< :prd:_{a} A <-> FunctionOn f a /\ forall x, x :< a -> f!x :< A!x.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros A a f. split; intros H1.
  - apply FromClass.Charac in H1. assumption.
  - apply FromClass.Charac. assumption.
Qed.

(* Every member of a product is a function on the index set.                    *)
Proposition IsFunctionOn : forall (A:Class) (a f:U),
  f :< :prd:_{a} A -> FunctionOn f a.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros A a f H1. apply Charac in H1. apply H1.
Qed.

(* Each value of a product member lies in the corresponding fibre.              *)
Proposition EvalIsIn : forall (A:Class) (a f x:U),
  f :< :prd:_{a} A -> x :< a -> f!x :< A!x.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros A a f x H1 H2. apply Charac in H1. apply H1; assumption.
Qed.

(* A function choosing from each fibre belongs to the product.                  *)
Proposition IsIn : forall (A:Class) (a f:U),
  FunctionOn f a                      ->
  (forall x, x :< a -> f!x :< A!x)    ->
  f :< :prd:_{a} A.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros A a f H1 H2. apply Charac. split; assumption.
Qed.

(* The product is the same when the two families agree on the index set.        *)
Proposition Equal : forall (A B:Class) (a:U),
  (forall x, x :< a -> A!x = B!x) -> :prd:_{a} A = :prd:_{a} B.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros A B a H1.
  (* A choice from A is a choice from B because the fibres agree.               *)
  assert (:prd:_{a} A :<=: :prd:_{a} B) as H2. {
    intros f H2. apply Charac in H2. destruct H2 as [H2 H3].
    apply Charac. split. 1: assumption.
    intros x H4. assert (A!x = B!x) as H5. { apply H1. assumption. }
    rewrite <- H5. apply H3. assumption. }
  (* The same argument with the equality reversed gives the converse.           *)
  assert (:prd:_{a} B :<=: :prd:_{a} A) as H3. {
    intros f H3. apply Charac in H3. destruct H3 as [H3 H4].
    apply Charac. split. 1: assumption.
    intros x H5. assert (A!x = B!x) as H6. { apply H1. assumption. }
    rewrite H6. apply H4. assumption. }
  apply Incl.Double. split; assumption.
Qed.

(* The product is invariant under class equivalence of the family.              *)
Proposition EquivCompat : forall (A B:Class) (a:U),
  A :~: B -> :prd:_{a} A = :prd:_{a} B.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros A B a H1. apply Equal. intros x H2.
  apply EvalOfClass.EquivCompat. assumption.
Qed.

(* Shrinking indices and enlarging fibres preserves product membership.         *)
Proposition InclCompat : forall (A B:Class) (a b f:U),
  a :<=: b                              ->
  (forall x, x :< a -> A!x :<=: B!x)    ->
  f     :< :prd:_{b} A                  ->
  f:|:a :< :prd:_{a} B.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros A B a b f H1 H2 H3. apply Charac.
  (* Restricting the original choice function gives a function on the smaller   *)
  (* index set.                                                                 *)
  assert (FunctionOn (f:|:a) a) as H4. {
    apply FunctionOn.Restrict with b. 2: assumption.
    apply IsFunctionOn with A. assumption. }
  (* On each remaining index, the restricted value is still the original value. *)
  assert (forall x, x :< a -> (f:|:a)!x :< B!x) as H5. {
    intros x H5.
    assert (FunctionOn f b) as H6. { apply IsFunctionOn with A. assumption. }
    assert (Functional f) as H7. { destruct H6 as [[_ H6] _]. assumption. }
    rewrite Restrict.Eval; try assumption.
    assert (f!x :< A!x) as H8. {
      apply (EvalIsIn A b f x). 1: assumption. apply H1. assumption. }
    apply H2; assumption. }
  split; assumption.
Qed.

(* Restricting a product member to a smaller index set preserves membership.    *)
Proposition InclCompatL : forall (A:Class) (a b f:U),
  a :<=: b -> f :< :prd:_{b} A -> f:|:a :< :prd:_{a} A.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros A a b f H1 H2. apply InclCompat with A b; try assumption.
  intros x H3. apply Incl.Refl.
Qed.

(* Enlarging each fibre enlarges the product over the same index set.           *)
Proposition InclCompatR : forall (A B:Class) (a:U),
  (forall x, x :< a -> A!x :<=: B!x) ->
  :prd:_{a} A :<=: :prd:_{a} B.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros A B a H1 f H2. apply (Charac A a f) in H2.
  destruct H2 as [H2 H3]. apply (Charac B a f). split. 1: assumption.
  intros x H4. apply H1. 1: assumption. apply H3. assumption.
Qed.

(* If all fibres are contained in b, then the product lies in map(a,b).         *)
Proposition WhenBounded : forall (A:Class) (a b:U),
  (forall x, x :< a -> A!x :<=: b) -> :prd:_{a} A :<=: map a b.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros A a b H1 f H2.
  (* The product member is already a function on the index set.                 *)
  assert (FunctionOn f a) as H3. { apply IsFunctionOn with A. assumption. }
  (* Every displayed value lies in the common bound b.                          *)
  assert (forall x, x :< a -> f!x :< b) as H4. {
    intros x H4. assert (A!x :<=: b) as H5. { apply H1. assumption. }
    apply H5. apply (EvalIsIn A a f x); assumption. }
  apply Map.CharacMap, Fun.FromFunctionOn; assumption.
Qed.

(* The product lies in the map set into the generalized union of its fibres.    *)
Proposition IsIncl : forall (A:Class) (a:U),
  :prd:_{a} A :<=: map a (:\/:_{a} A).
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros A a. apply WhenBounded. intros x H1.
  apply UnionGenOfClass.IsIncl. assumption.
Qed.

(* A product over a constant family is the ordinary map set.                    *)
Proposition WhenConstant : forall (A:Class) (a b:U),
  (forall x, x :< a -> A!x = b) -> :prd:_{a} A = map a b.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros A a b H1.
  (* Every product member maps into the displayed constant fibre.               *)
  assert (:prd:_{a} A :<=: map a b) as H2. {
    apply WhenBounded. intros x H2.
    assert (A!x = b) as H3. { apply H1. assumption. }
    rewrite H3. apply Incl.Refl. }
  (* Conversely, any map into b chooses from the equal fibre at every index.    *)
  assert (map a b :<=: :prd:_{a} A) as H3. {
    intros f H3. apply Map.CharacMap in H3. apply Charac. split. 1: apply H3.
    intros x H4. assert (A!x = b) as H5. { apply H1. assumption. }
    rewrite H5. apply Fun.IsInRange with a; assumption. }
  apply Incl.Double. split; assumption.
Qed.

(* The product over the empty index set is the singleton empty function.        *)
Proposition WhenZeroL : forall (A:Class), :prd:_{:0:} A = :{:0:}:.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros A.
  (* Every function on the empty index set is the empty function.               *)
  assert (:prd:_{:0:} A :<=: :{:0:}:) as H1. {
    intros f H1. apply Single.Charac.
    apply FunctionOn.Equal with :0: :0:; try reflexivity.
    - apply IsFunctionOn with A. assumption.
    - apply FunctionOn.WhenZero. reflexivity.
    - intros x H2. apply Empty.Charac in H2. contradiction. }
  (* The empty function chooses from every empty list of fibres.                *)
  assert (:{ :0: }: :<=: :prd:_{:0:} A) as H2. {
    intros f H2. apply Single.Charac in H2. apply Charac. split.
    - apply FunctionOn.WhenZero. assumption.
    - intros x H3. apply Empty.Charac in H3. contradiction. }
  apply Incl.Double. split; assumption.
Qed.

(* A product is empty when one of its fibres over the index set is empty.       *)
Proposition WhenZeroR : forall (A:Class) (a x:U),
  x :< a -> A!x = :0: -> :prd:_{a} A = :0:.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros A a x H1 H2. apply Incl.Double. split; intros f H3.
  - (* A choice function would have to choose an element of the empty fibre.    *)
    assert (f!x :< A!x) as H4. { apply EvalIsIn with a; assumption. }
    rewrite H2 in H4. apply Empty.Charac in H4. contradiction.
  - apply Empty.Charac in H3. contradiction.
Qed.

(* The product is unchanged by eta-reducing the family.                         *)
Proposition EtaReduce : forall (A:Class) (a:U),
  :prd:_{a} :[fun x => A!x]: = :prd:_{a} A.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros A a. apply Equal. intros x H1. apply Class.Relation.Fun.From.Eval.
Qed.

