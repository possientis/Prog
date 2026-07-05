Require Import ZF.Class.Equiv.
Require Import ZF.Class.Relation.Fun.From2.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Prod.
Require Import ZF.Set.Relation.Bij.
Require Import ZF.Set.Relation.Bijection.
Require Import ZF.Set.Relation.BijectionOn.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Fun.
Require Import ZF.Set.Relation.Function.
Require Import ZF.Set.Relation.Functional.
Require Import ZF.Set.Relation.FunctionOn.
Require Import ZF.Set.Relation.Inj.
Require Import ZF.Set.Relation.OneToOne.
Require Import ZF.Set.Relation.Onto.
Require Import ZF.Set.Relation.Range.
Require Import ZF.Set.Relation.Relation.
Require Import ZF.Set.Relation.RestrictOfClass.

Require Import ZF.Notation.Eval.

Module CF2 := ZF.Class.Relation.Fun.From2.
Module SRR := ZF.Set.Relation.RestrictOfClass.

(* Given sets a and b and a Coq expression f representing a function with two   *)
(* argument sets, we define the associated function with domain a x b.          *)
Definition from2 (a b:U) (f:U -> U -> U) : U := (CF2.from2 f) :|: (a :x: b).

(* The binary expression has all its values in the target set.                  *)
Definition MapsTo (f:U -> U -> U) (a b c:U) : Prop :=
  forall u v, u :< a -> v :< b -> f u v :< c.

(* The binary expression separates pairs of arguments on the domain product.    *)
Definition Injective (f:U -> U -> U) (a b:U) : Prop :=
  forall u v u' v',
    u  :< a -> v  :< b ->
    u' :< a -> v' :< b ->
    f u v = f u' v' -> :(u,v): = :(u',v'):.

(* The binary expression displays every element of the target set.              *)
Definition Surjective (f:U -> U -> U) (a b c:U) : Prop :=
  forall w, w :< c -> exists u v, u :< a /\ v :< b /\ f u v = w.


(* x belongs to from2 iff x = ((u,v), f u v) for some u in a and v in b.        *)
Proposition Charac : forall (f:U -> U -> U) (a b x:U),
  x :< from2 a b f <-> exists u v, x = :(:(u,v):,f u v): /\ u :< a /\ v :< b.
Proof.
  intros f a b x. split; intros H1.
  - apply SRR.Charac in H1. 2: apply CF2.IsFunctional.
    destruct H1 as [y [z [H1 [H2 H3]]]].
    apply Prod.Charac in H2. destruct H2 as [u [v [H2 [H4 H5]]]].
    apply CF2.Charac2 in H3. destruct H3 as [u' [v' [H3 H6]]].
    subst. apply OrdPair.Equal in H3. destruct H3 as [H3 H7]. subst.
    exists u', v'. split. 1: reflexivity. split; assumption.
  - destruct H1 as [u [v [H1 [H2 H3]]]].
    apply SRR.CharacRev with :(u,v): (f u v); try assumption.
    + apply CF2.IsFunctional.
    + apply Prod.Charac. exists u, v. split. 1: reflexivity. split; assumption.
    + apply CF2.Satisfies.
Qed.

Proposition Charac2 : forall (f:U -> U -> U) (a b x y:U),
  :(x,y): :< from2 a b f <->
  exists u v, x = :(u,v): /\ y = f u v /\ u :< a /\ v :< b.
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)
  (* Membership as a pair unpacks the witnesses via ordered-pair injectivity.   *)
  intros f a b x y. split; intros H1.
  - apply Charac in H1. destruct H1 as [u [v [H1 [H2 H3]]]].
    apply OrdPair.Equal in H1. destruct H1 as [H1 H4]. subst.
    exists u, v. split. 1: reflexivity.
    split. 1: reflexivity. split; assumption.
  - destruct H1 as [u [v [H1 [H2 [H3 H4]]]]]. subst.
    apply Charac. exists u, v. split. 1: reflexivity. split; assumption.
Qed.

Proposition Charac3 : forall (f:U -> U -> U) (a b u v w:U),
  :(:(u,v):,w): :< from2 a b f <-> u :< a /\ v :< b /\ w = f u v.
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)
  (* Follows from the pair-level characterization by ordered-pair injectivity.  *)
  intros f a b u v w. split; intros H1.
  - apply Charac2 in H1. destruct H1 as [u' [v' [H1 [H2 [H3 H4]]]]].
    apply OrdPair.Equal in H1. destruct H1 as [Hu Hv]. subst u'. subst v'.
    split. 1: assumption. split; assumption.
  - destruct H1 as [H1 [H2 H3]]. subst. apply Charac2.
    exists u, v. split. 1: reflexivity.
    split. 1: reflexivity. split; assumption.
Qed.

(* The pair ((u,v), f(u,v)) belongs to from2 a b f when u in a and v in b.      *)
Proposition Satisfies : forall (f:U -> U -> U) (a b u v:U),
  u :< a -> v :< b -> :(:(u,v):, f u v): :< from2 a b f.
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)
  (* Follows directly from the membership characterization.                     *)
  intros f a b u v H1 H2. apply Charac3.
  split. 1: assumption. split. 1: assumption. reflexivity.
Qed.

(* The relation from2 a b f is a function on the product a x b.                 *)
Proposition IsFunctionOn : forall (f:U -> U -> U) (a b:U),
  FunctionOn (from2 a b f) (a :x: b).
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)
  intros f a b. apply SRR.IsFunctionOn. 1: apply CF2.IsFunctional.
  intros p H1. apply Prod.Charac in H1.
  destruct H1 as [u [v [H1 [H2 H3]]]]. subst.
  apply CF2.DomainOf.
Qed.

(* The value of from2 a b f at (u,v) equals f u v when u in a and v in b.       *)
Proposition Eval : forall (f:U -> U -> U) (a b u v:U),
  u :< a -> v :< b -> (from2 a b f)!(:(u,v):) = f u v.
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)
  intros f a b u v H1 H2.
  apply (FunctionOn.Eval (from2 a b f) (a :x: b)).
  - apply IsFunctionOn.
  - apply Satisfies; assumption.
Qed.

(* The domain of the binary function is the product of the two domains.         *)
Proposition DomainOf : forall (f:U -> U -> U) (a b:U),
  domain (from2 a b f) = a :x: b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros f a b.
  (* The function-on statement already contains the claimed domain equality.    *)
  assert (FunctionOn (from2 a b f) (a :x: b)) as H1. { apply IsFunctionOn. }
  apply H1.
Qed.

(* The binary function is a relation.                                           *)
Proposition IsRelation : forall (f:U -> U -> U) (a b:U),
  Relation (from2 a b f).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros f a b.
  (* A function on a domain is, in particular, a relation.                      *)
  assert (FunctionOn (from2 a b f) (a :x: b)) as H1. { apply IsFunctionOn. }
  destruct H1 as [[H1 _] _]. assumption.
Qed.

(* The binary function is functional.                                           *)
Proposition IsFunctional : forall (f:U -> U -> U) (a b:U),
  Functional (from2 a b f).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros f a b.
  (* A function on a domain assigns at most one value to each argument.         *)
  assert (FunctionOn (from2 a b f) (a :x: b)) as H1. { apply IsFunctionOn. }
  apply H1.
Qed.

(* The binary function is a function.                                           *)
Proposition IsFunction : forall (f:U -> U -> U) (a b:U),
  Function (from2 a b f).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros f a b.
  (* A function on a domain is, in particular, a function.                      *)
  assert (FunctionOn (from2 a b f) (a :x: b)) as H1. { apply IsFunctionOn. }
  apply H1.
Qed.

(* If all values lie in c, then from2 defines a function a x b -> c.            *)
Proposition IsFun : forall (f:U -> U -> U) (a b c:U),
  MapsTo f a b c -> Fun (from2 a b f) (a :x: b) c.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros f a b c H1. split. 1: apply IsFunctionOn.
  (* Every element of the range is one of the displayed values f(u,v).          *)
  intros y H2. apply Range.Charac in H2. destruct H2 as [x H2].
  apply Charac2 in H2. destruct H2 as [u [v [H2 [H3 [H4 H5]]]]]. subst y.
  apply H1; assumption.
Qed.

(* If the expression separates pairs, the function is one-to-one.               *)
Proposition IsOneToOne : forall (f:U -> U -> U) (a b:U),
  Injective f a b -> OneToOne (from2 a b f).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros f a b H1. apply FunctionOn.IsOneToOne with (a :x: b).
  - apply IsFunctionOn.
  - (* Product arguments are displayed pairs, so equal values separate them.    *)
    intros x y H2 H3 H4. apply Prod.Charac in H2.
    destruct H2 as [u [v [H2 [H5 H6]]]]. apply Prod.Charac in H3.
    destruct H3 as [u' [v' [H3 [H7 H8]]]]. subst x. subst y.
    rewrite Eval in H4. 2: assumption. 2: assumption.
    rewrite Eval in H4. 2: assumption. 2: assumption.
    apply H1; assumption.
Qed.

(* If the expression separates pairs, then the relation is a bijection.         *)
Proposition IsBijection : forall (f:U -> U -> U) (a b:U),
  Injective f a b -> Bijection (from2 a b f).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros f a b H1. split.
  - apply IsRelation.
  - apply IsOneToOne. assumption.
Qed.

(* If the expression separates pairs, then it is a bijection on a x b.          *)
Proposition IsBijectionOn : forall (f:U -> U -> U) (a b:U),
  Injective f a b -> BijectionOn (from2 a b f) (a :x: b).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros f a b H1. split.
  - apply IsBijection. assumption.
  - apply DomainOf.
Qed.

(* If the values lie in c and separate pairs, we get an injection a x b -> c.   *)
Proposition IsInj : forall (f:U -> U -> U) (a b c:U),
  MapsTo f a b c                         ->
  Injective f a b                        ->
  Inj (from2 a b f) (a :x: b) c.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros f a b c H1 H2. split.
  - apply IsBijectionOn. assumption.
  - (* The range is contained in c because every displayed value lies in c.     *)
    intros y H3. apply Range.Charac in H3. destruct H3 as [x H3].
    apply Charac2 in H3. destruct H3 as [u [v [H3 [H4 [H5 H6]]]]]. subst y.
    apply H1; assumption.
Qed.

(* If the expression has exactly the values in c, it is onto c.                 *)
Proposition IsOnto : forall (f:U -> U -> U) (a b c:U),
  MapsTo f a b c                          ->
  Surjective f a b c                      ->
  Onto (from2 a b f) (a :x: b) c.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros f a b c H1 H2. split. 1: apply IsFunctionOn.
  apply Incl.Double. split.
  - (* All displayed values lie in c.                                           *)
    intros y H3. apply Range.Charac in H3. destruct H3 as [x H3].
    apply Charac2 in H3. destruct H3 as [u [v [H3 [H4 [H5 H6]]]]]. subst y.
    apply H1; assumption.
  - (* Every element of c is displayed by some pair in the product.             *)
    intros y H3. apply H2 in H3. destruct H3 as [u [v [H3 [H4 H5]]]].
    apply Range.Charac. exists :(u,v):. rewrite <- H5. apply Satisfies; assumption.
Qed.

(* If the expression is injective and has values c, it is a bijection.          *)
Proposition IsBij : forall (f:U -> U -> U) (a b c:U),
  MapsTo f a b c                         ->
  Injective f a b                        ->
  Surjective f a b c                     ->
  Bij (from2 a b f) (a :x: b) c.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros f a b c H1 H2 H3. split.
  - apply IsBijectionOn. assumption.
  - apply IsOnto; assumption.
Qed.
