Declare Scope ZF_Set_Product_scope.
Open    Scope ZF_Set_Product_scope.

Require Import ZF.Set.
Require Import ZF.Class.Bounded.
Require Import ZF.Class.Small.
Require Import ZF.Set.Include.
Require Import ZF.Set.Intersect.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Pair.
Require Import ZF.Set.Power.
Require Import ZF.Set.Singleton.
Require Import ZF.Set.Union.

(* It is useful to define the predicate underlying the product of two sets.     *)
Definition ProdPred (a b:U) : U -> Prop := fun x =>
  exists y, exists z, y :< a /\ z :< b /\ x = :(y,z):.

(* The product predicate of sets a and b is small.                              *)
Proposition ProdSmall : forall (a b:U),
  Small (ProdPred a b).
Proof.
  (* Let a and b be two sets *)
  intros a b.

  (* To show a class is small, it is sufficient to prove it is bounded *)
  apply BoundedClassIsSmall.

  (* So we need to show the existence of c such that ProdPred a b x -> x :< c   *)
  assert (exists c, forall x, ProdPred a b x -> x :< c) as A. 2: apply A.

  (* Consider the set c = P(P(a\/b)) *)
  remember :P(:P(a:\/:b)) as c eqn:Hc.

  (* We claim that c has the desired property *)
  exists c.

  (* We need to show that ProdPred a b x -> x :< c for all x *)
  assert (forall x, ProdPred a b x -> x :< c) as A. 2: apply A.

  (* So let x be an arbitrary set satisfying the predicate ProdPred a b *)
  intros x H1.

  (* Then we have some y and z such that y :< a, z :< b and x = (y,z) *)
  destruct H1 as [y [z [Hya [Hzb H1]]]].

  (* So we have y :< a *)
  assert (y :< a) as A. { apply Hya. } clear A.

  (* And we have z :< b *)
  assert (z :< b) as A. { apply Hzb. } clear A.

  (* And x is the ordered pair (y,z) *)
  assert (x = :(y,z):) as A. { apply H1. } clear A.

  (* So we need to show that x :< P(P(a\/b)) *)
  rewrite Hc.
  assert (x :< :P(:P(a:\/:b))) as A. 2: apply A.

  (* In other words, we need to show that (y,z) <= P(a\/b) *)
  apply PowerCharac. rewrite H1.
  assert (:(y,z): :<=: :P(a:\/:b)) as A. 2: apply A.

  (* So let u be an element of (y,z) *)
  intros u H2. apply OrdPairCharac in H2.

  (* Since (y,z) = {{y},{y,z}} we have u = {y} or u = {y,z} *)
  assert (u = :{y}: \/ u = :{y,z}: ) as A. { apply H2. } clear A.

  (* And we need to show that u is an element of P(a\/b) *)
  assert (u :< :P(a:\/:b)) as A. 2: apply A.

  (* In other words, we need to show that u <= a\/b *)
  apply PowerCharac.
  assert (u :<=: a:\/:b) as A. 2: apply A.

  (* We consider the cases u = {y} and u = {y,z} separately *)
  destruct H2 as [H2|H2]; rewrite H2.

  (* case u = {y} : we need to show that {y} <= a\/b, given that y :< a *)
  - assert (:{y}: :<=: a:\/:b) as A. 2: apply A.
    intros v H3. apply SingleCharac in H3. apply UnionCharac.
    subst. left. apply Hya.

  (* case u = {y,z} : we need to show that {y,z} <= a\/b with y :< a and z :< b *)
  - assert (:{y,z}: :<=: a:\/:b) as A. 2: apply A.
    intros v H3. apply PairCharac in H3. apply UnionCharac.
    destruct H3 as [H3|H3]; subst.
    + left.  apply Hya.
    + right. apply Hzb.
Qed.

(* We consider the set defined by the product predicate of the sets a and b     *)
Definition prodSet (a b:U) : U
  := toSet (ProdPred a b) (ProdSmall a b).

Notation "a :x: b" := (prodSet a b)
  (at level 11, right associativity) : ZF_Set_Product_scope.

(* Characterisation of the elements of the product axb *)
Proposition ProdCharac : forall (a b:U),
  forall x, x :< a :x: b <-> exists y, exists z, y :< a /\ z :< b /\ x =:(y,z):.
Proof.
  unfold prodSet. intros a b. apply ClassCharac.
Qed.

Proposition ProdCharac2 : forall (a b:U),
  forall y, forall z, :(y,z): :< a :x: b <-> y :< a /\ z :< b.
Proof.
  intros a b y z. split; intros H1.
  - apply ProdCharac in H1. destruct H1 as [y' [z' [Hya [Hzb H1]]]].
    apply OrdPairEqual in H1. destruct H1 as [H1 H2]. subst. split; assumption.
  - destruct H1 as [Hya Hzb]. apply ProdCharac. exists y. exists z. split.
    + apply Hya.
    + split.
      * apply Hzb.
      * reflexivity.
Qed.

Proposition IntersectProdIsProdIntersect: forall (a1 a2 b1 b2:U),
  (a1:x:b1) :/\: (a2:x:b2) = (a1:/\:a2) :x: (b1:/\:b2).
Proof.
  intros a1 a2 b1 b2. apply DoubleInclusion. split; intros x H1.
  - apply IntersectCharac in H1. destruct H1 as [H1 H2].
    apply ProdCharac in H1. destruct H1 as [y1 [z1 [H1 [H1' G1]]]].
    apply ProdCharac in H2. destruct H2 as [y2 [z2 [H2 [H2' G2]]]].
    subst. apply OrdPairEqual in G2. destruct G2 as [G1 G2]. subst.
    apply ProdCharac2. split; apply IntersectCharac; split; assumption.
  - apply ProdCharac in H1. destruct H1 as [y [z [Ha [Hb H1]]]].
    apply IntersectCharac in Ha. destruct Ha as [Ha Ha'].
    apply IntersectCharac in Hb. destruct Hb as [Hb Hb'].
    apply IntersectCharac. split; apply ProdCharac; exists y; exists z; split.
    + apply Ha.
    + split; assumption.
    + apply Ha'.
    + split; assumption.
Qed.
