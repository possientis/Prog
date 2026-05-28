Require Import ZF.Class.Equiv.
Require Import ZF.Class.Prod.
Require Import ZF.Class.Relation.Fun.From2.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Inter2.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Fun.
Require Import ZF.Set.Relation.Image.
Require Import ZF.Set.Relation.Range.
Require Import ZF.Set.Relation.Relation.
Require Import ZF.Set.Relation.RestrictOfClass.
Require Import ZF.Set.Union2.
Require Import ZF.Notation.Eval.
Export ZF.Notation.Prod.

Module CF2 := ZF.Class.Relation.Fun.From2.
Module SRF := ZF.Set.Relation.RestrictOfClass.

(* We consider the set defined by the product predicate of the sets a and b     *)
Definition prod (a b:U) : U := fromClass (toClass a :x: toClass b)
  (IsSmall (toClass a) (toClass b) (SetIsSmall a) (SetIsSmall b)).

(* Notation "a :x: b" := (prod a b)                                             *)
Global Instance SetProd : Prod U := { prod := prod }.

(* The first projection from a product to its left component.                   *)
Definition fst (a b:U) : U := (CF2.from2 (fun x _ => x)) :|: (a :x: b).

(* The second projection from a product to its right component.                 *)
Definition snd (a b:U) : U := (CF2.from2 (fun _ y => y)) :|: (a :x: b).

(* The class of the product a x b equals the product of the classes.            *)
Proposition ToClass : forall (a b:U),
  toClass (a :x: b) :~: toClass a :x: toClass b.
Proof.
  intros a b. apply FromClass.ToClass.
Qed.

(* Characterisation of the elements of the product a x b.                       *)
Proposition Charac : forall (a b:U),
  forall x, x :< a :x: b <-> exists y, exists z, x = :(y,z): /\ y :< a /\ z :< b.
Proof.
  intros a b x. split; intros H1.
  - apply FromClass.Charac in H1. assumption.
  - apply FromClass.Charac. assumption.
Qed.

(* The ordered pair (y,z) belongs to a x b iff y is in a and z is in b.         *)
Proposition Charac2 : forall (a b y z:U),
  :(y,z): :< a :x: b <-> y :< a /\ z :< b.
Proof.
  intros a b y z. split; intros H1.
  - apply Charac in H1. destruct H1 as [y' [z' [H1 [Hya Hzb]]]].
    apply OrdPair.Equal in H1. destruct H1 as [H1 H2]. subst. split; assumption.
  - destruct H1 as [Hya Hzb]. apply Charac. exists y, z. split.
    + reflexivity.
    + split; assumption.
Qed.

(* The product of two sets is compatible with inclusion.                        *)
Proposition InclCompat : forall (a b c d:U),
  a :<=: b -> c :<=: d -> a :x: c :<=: b :x: d.
Proof.
  intros a b c d H1 H2 x H3. apply Charac in H3.
  destruct H3 as [y [z [H3 [H4 H5]]]]. apply Charac. exists y, z.
  split. 1: assumption. split.
  - apply H1. assumption.
  - apply H2. assumption.
Qed.

(* The product of two sets is left-compatible with inclusion.                   *)
Proposition InclCompatL : forall (a b c:U),
  a :<=: b -> a :x: c :<=: b :x: c.
Proof.
  intros a b c H1. apply InclCompat. 1: assumption.
  apply Incl.Refl.
Qed.

(* The product of two sets is right-compatible with inclusion.                  *)
Proposition InclCompatR : forall (a b c:U),
  a :<=: b -> c :x: a :<=: c :x: b.
Proof.
  intros a b c H1. apply InclCompat. 2: assumption.
  apply Incl.Refl.
Qed.

(* A relation is a subset of the product of its domain and image thereof.       *)
Proposition IsInclRel : forall (f:U),
  Relation f -> f :<=: (domain f) :x: f:[domain f]:.
Proof.
  intros f H1 x H3. specialize (H1 x H3). destruct H1 as [y [z H1]].
  apply Charac. exists y, z. split. 1: assumption. subst. split.
  - apply Domain.Charac. exists z. assumption.
  - apply Image.Charac. exists y. split. 2: assumption.
    apply Domain.Charac. exists z. assumption.
Qed.

(* A function f:a -> b is a subset of a x b.                                    *)
Proposition IsInclFun : forall (f a b:U),
  Fun f a b -> f :<=: a :x: b.
Proof.
  intros f a b H1. apply ZF.Set.Incl.Tran with (a :x: f:[a]:).
  - destruct H1 as [[H1 H2] _]. rewrite <- H2. apply IsInclRel. apply H1.
  - apply InclCompatR. rewrite (Fun.ImageOfDomain f a b).
    2: assumption. apply H1.
Qed.

(* The first projection is a function from a x b to a.                          *)
Proposition IsFunFst : forall (a b:U), Fun (fst a b) (a :x: b) a.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b. split.
  - unfold fst. apply SRF.IsFunctionOn.
    + apply CF2.IsFunctional.
    + intros p H1. apply Charac in H1.
      destruct H1 as [x [y [H1 [H2 H3]]]]. subst. apply CF2.DomainOf.
  - intros y H1. unfold fst in H1. apply Range.Charac in H1.
    destruct H1 as [p H1]. apply SRF.Charac2 in H1.
    2: apply CF2.IsFunctional. destruct H1 as [H1 H2].
    apply Charac in H1. destruct H1 as [u [v [H1 [H3 H4]]]].
    apply CF2.Charac2 in H2. destruct H2 as [u' [v' [H2 H5]]]. subst y.
    rewrite H1 in H2. apply OrdPair.Equal in H2. destruct H2 as [H2 _].
    rewrite <- H2. assumption.
Qed.

(* The second projection is a function from a x b to b.                         *)
Proposition IsFunSnd : forall (a b:U), Fun (snd a b) (a :x: b) b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b. split.
  - unfold snd. apply SRF.IsFunctionOn.
    + apply CF2.IsFunctional.
    + intros p H1. apply Charac in H1.
      destruct H1 as [x [y [H1 [H2 H3]]]]. subst. apply CF2.DomainOf.
  - intros y H1. unfold snd in H1. apply Range.Charac in H1.
    destruct H1 as [p H1]. apply SRF.Charac2 in H1.
    2: apply CF2.IsFunctional. destruct H1 as [H1 H2].
    apply Charac in H1. destruct H1 as [u [v [H1 [H3 H4]]]].
    apply CF2.Charac2 in H2. destruct H2 as [u' [v' [H2 H5]]]. subst y.
    rewrite H1 in H2. apply OrdPair.Equal in H2. destruct H2 as [_ H2].
    rewrite <- H2. assumption.
Qed.

(* The first projection sends (x,y) to x.                                       *)
Proposition EvalFst : forall (a b x y:U),
  x :< a -> y :< b -> (fst a b)!(:(x,y):) = x.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b x y H1 H2. unfold fst. rewrite SRF.Eval.
  - apply CF2.Eval.
  - apply CF2.IsFunctional.
  - apply Charac2. split; assumption.
Qed.

(* The second projection sends (x,y) to y.                                      *)
Proposition EvalSnd : forall (a b x y:U),
  x :< a -> y :< b -> (snd a b)!(:(x,y):) = y.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b x y H1 H2. unfold snd. rewrite SRF.Eval.
  - apply CF2.Eval.
  - apply CF2.IsFunctional.
  - apply Charac2. split; assumption.
Qed.

(* The product with the empty set on the left is empty.                         *)
Proposition ZeroL : forall (a:U), :0: :x: a = :0:.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a. apply Incl.Double. split. 2: apply Empty.IsIncl.
  intros x H1. apply Charac in H1. destruct H1 as [y [z [H1 [H2 H3]]]].
  apply Empty.Charac in H2. contradiction.
Qed.

(* The product with the empty set on the right is empty.                        *)
Proposition ZeroR : forall (a:U), a :x: :0: = :0:.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a. apply Incl.Double. split. 2: apply Empty.IsIncl.
  intros x H1. apply Charac in H1. destruct H1 as [y [z [H1 [H2 H3]]]].
  apply Empty.Charac in H3. contradiction.
Qed.

(* Product distributes on the left over binary union.                           *)
Proposition DistribL : forall (a b c:U),
  a :x: (b :\/: c) = a :x: b :\/: a :x: c.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c. apply Incl.Double. split; intros x H1.
  - apply Charac in H1. destruct H1 as [y [z [H1 [H2 H3]]]].
    apply Union2.Charac in H3. apply Union2.Charac.
    destruct H3 as [H3|H3].
    + left. apply Charac. exists y, z. split. 1: assumption.
      split; assumption.
    + right. apply Charac. exists y, z. split. 1: assumption.
      split; assumption.
  - apply Union2.Charac in H1. apply Charac.
    destruct H1 as [H1|H1]; apply Charac in H1;
    destruct H1 as [y [z [H1 [H2 H3]]]]; exists y; exists z;
    split. 1,3: assumption.
    + split. 1: assumption. apply Union2.Charac. left. assumption.
    + split. 1: assumption. apply Union2.Charac. right. assumption.
Qed.

(* Product distributes on the right over binary union.                          *)
Proposition DistribR : forall (a b c:U),
  (a :\/: b) :x: c = a :x: c :\/: b :x: c.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c. apply Incl.Double. split; intros x H1.
  - apply Charac in H1. destruct H1 as [y [z [H1 [H2 H3]]]].
    apply Union2.Charac in H2. apply Union2.Charac.
    destruct H2 as [H2|H2].
    + left. apply Charac. exists y, z. split. 1: assumption.
      split; assumption.
    + right. apply Charac. exists y, z. split. 1: assumption.
      split; assumption.
  - apply Union2.Charac in H1. apply Charac.
    destruct H1 as [H1|H1]; apply Charac in H1;
    destruct H1 as [y [z [H1 [H2 H3]]]]; exists y; exists z;
    split. 1,3: assumption.
    + split. 2: assumption. apply Union2.Charac. left. assumption.
    + split. 2: assumption. apply Union2.Charac. right. assumption.
Qed.

(* The intersection of products equals the product of intersections.            *)
Proposition Inter : forall (a1 a2 b1 b2:U),
  a1 :x: b1 :/\: a2 :x: b2 = (a1 :/\: a2) :x: (b1 :/\: b2).
Proof.
  intros a1 a2 b1 b2. apply Incl.Double. split; intros x H1.
  - apply Inter2.Charac in H1. destruct H1 as [H1 H2].
    apply Charac in H1. destruct H1 as [y1 [z1 [G1 [H1 H1']]]].
    apply Charac in H2. destruct H2 as [y2 [z2 [G2 [H2 H2']]]].
    subst. apply OrdPair.Equal in G2. destruct G2 as [G1 G2]. subst.
    apply Charac2. split; apply Inter2.Charac; split; assumption.
  - apply Charac in H1. destruct H1 as [y [z [H1 [Ha Hb]]]].
    apply Inter2.Charac in Ha. destruct Ha as [Ha Ha'].
    apply Inter2.Charac in Hb. destruct Hb as [Hb Hb'].
    apply Inter2.Charac. split; apply Charac; exists y; exists z; split.
    + assumption.
    + split; assumption.
    + assumption.
    + split; assumption.
Qed.

