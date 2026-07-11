Require Import ZF.Class.Equiv.
Require Import ZF.Class.Relation.Fun.
Require Import ZF.Class.Relation.Range.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Inter2.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Compose.
Require Import ZF.Set.Relation.Converse.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.FunctionOn.
Require Import ZF.Set.Relation.Image.
Require Import ZF.Set.Relation.OneToOne.
Require Import ZF.Set.Relation.Range.
Require Import ZF.Set.Relation.Restrict.
Require Import ZF.Set.Single.

Module CRF := ZF.Class.Relation.Fun.
Module CRR := ZF.Class.Relation.Range.

(* f is a function from a to b.                                                 *)
Definition Fun (f a b:U) : Prop := FunctionOn f a /\ range f :<=: b.

(* If the set is a function from a to be, then so is the class.                 *)
Proposition ToClass : forall (f a b:U),
  Fun f a b -> CRF.Fun (toClass f) (toClass a) (toClass b).
Proof.
  intros f a b [H1 H2]. split.
  - apply FunctionOn.ToClass. assumption.
  - apply Incl.EquivCompatL with (toClass (range f)).
    2: assumption. apply Range.ToClass.
Qed.

(* If the class is a function from a to b, then so is the set.                  *)
Proposition FromClass : forall (f a b:U),
  CRF.Fun (toClass f) (toClass a) (toClass b) -> Fun f a b.
Proof.
  intros f a b [H1 H2]. split.
  - apply FunctionOn.FromClass. assumption.
  - apply Incl.ToClass, Incl.EquivCompatL with (CRR.range (toClass f)).
    2: assumption. apply Equiv.Sym, Range.ToClass.
Qed.

(* A function remains a function after enlarging the codomain.                  *)
Proposition InclCompatR : forall (f a b c:U),
  b :<=: c -> Fun f a b -> Fun f a c.
Proof.
  intros f a b c H1 [H2 H3]. split. 1: assumption.
  apply Incl.Tran with b; assumption.
Qed.

(* A function f:a -> b that is injective on a is one-to-one.                    *)
Proposition IsOneToOne : forall (f a b:U),
  Fun f a b                                             ->
  (forall x y, x :< a -> y :< a -> f!x = f!y -> x = y)  ->
  OneToOne f.
Proof.
  intros f a b H1. apply FunctionOn.IsOneToOne, H1.
Qed.

(* Two functions with the same domains and which coincide pointwise are equal.  *)
Proposition Equal : forall (f a b g c d:U),
  Fun f a b                       ->
  Fun g c d                       ->
  a = c                           ->
  (forall x, x :< a -> f!x = g!x) ->
  f = g.
Proof.
  intros f a b g c d [H1 _] [H2 _]. apply FunctionOn.Equal; assumption.
Qed.

(* The direct image of the domain is the range.                                 *)
Proposition ImageOfDomain : forall (f a b:U),
  Fun f a b -> f:[a]: = range f.
Proof.
  intros f a b [H1 _]. apply FunctionOn.ImageOfDomain. assumption.
Qed.

(* The image of any subset of the domain lies inside the codomain.              *)
Proposition ImageIncl : forall (f a b c:U),
  Fun f a b -> c :<=: a -> f:[c]: :<=: b.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros f a b c H1 H2.
  (* Every image element lies in the range, and the range lies in the codomain. *)
  apply Incl.Tran with (range f).
  - apply Range.ImageIsIncl.
  - apply H1.
Qed.


(* The inverse image of the range is the domain.                                *)
Proposition InvImageOfRange : forall (f a b:U),
  Fun f a b -> f^:-1::[range f]: = a.
Proof.
  intros f a b H1. apply FunctionOn.InvImageOfRange, H1.
Qed.

(* If f:a -> b and g:b -> c then g.f : a -> c.                                  *)
Proposition Compose : forall (f g a b c:U),
  Fun f a b             ->
  Fun g b c             ->
  Fun (g :.: f) a c.
Proof.
  intros f g a b c [H1 H2] [H3 H4]. split.
  - apply FunctionOn.Compose with b; assumption.
  - apply ZF.Set.Incl.Tran with (range g). 2: assumption.
    apply Compose.RangeIsSmaller.
Qed.

Proposition Eval' : forall (f a b x y:U),
  Fun f a b -> x :< a -> :(x,y): :< f <-> f!x = y.
Proof.
  intros f a b x y H1. apply FunctionOn.Eval', H1.
Qed.

(* If (x,y) belongs to a function f:a -> b then f(x) = y.                       *)
Proposition Eval : forall (f a b x y:U),
  Fun f a b -> :(x,y): :< f -> f!x = y.
Proof.
  intros f a b x y H1 H2. apply Eval' with a b; try assumption.
  assert (domain f = a) as H3. { apply H1. }
  rewrite <- H3. apply Domain.Charac. exists y. assumption.
Qed.

(* The ordered pair (x,f(x)) lies in the set f when x in a.                     *)
Proposition Satisfies : forall (f a b x:U),
  Fun f a b -> x :< a -> :(x,f!x): :< f.
Proof.
  intros f a b x H1. apply FunctionOn.Satisfies, H1.
Qed.

(* The value at x of a function defined on a lies in b  when x im a.            *)
Proposition IsInRange : forall (f a b x:U),
  Fun f a b -> x :< a -> f!x :< b.
Proof.
  intros f a b x H1 H2. apply H1.
  apply FunctionOn.IsInRange with a. 2: assumption. apply H1.
Qed.

(* y lies in f[c] iff y = f(x) for some x in both c and the domain a.           *)
Proposition ImageCharac : forall (f a b c:U), Fun f a b ->
  forall y, y :< f:[c]: <-> exists x, x :< c /\ x :< a /\ f!x = y.
Proof.
  intros f a b c H1. apply FunctionOn.ImageCharac, H1.
Qed.

(* The domain of g.f is the domain of f.                                        *)
Proposition DomainOfCompose : forall (f g a b c:U),
  Fun f a b             ->
  Fun g b c             ->
  domain (g :.: f) = a.
Proof.
  intros f g a b c [H1 H2] [H3 H4]. apply Incl.Double. split; intros x H5.
  - apply (FunctionOn.DomainOfCompose f g a b x H1 H3) in H5.
    destruct H5 as [H5 H6]. assumption.
  - apply (FunctionOn.DomainOfCompose f g a b x); try assumption.
    split. 1: assumption. apply IsInRange with a. 2: assumption.
    split; assumption.
Qed.

(* The value at x of g.f is the value at f(x) of g when x in a.                 *)
Proposition ComposeEval : forall (f g a b c x:U),
  Fun f a b               ->
  Fun g b c               ->
  x :< a                  ->
  (g :.: f)!x = g!(f!x).
Proof.
  intros f g a b c x [H1 H2] [H3 H4] H5.
  apply (FunctionOn.ComposeEval f g a b); try assumption.
  apply IsInRange with a. 2: assumption. split; assumption.
Qed.

(* Characterisation of the range of f.                                          *)
Proposition RangeCharac : forall (f a b y:U),
  Fun f a b -> y :< range f <-> exists x, x :< a /\ f!x = y.
Proof.
  intros f a b y H1. apply FunctionOn.RangeCharac, H1.
Qed.

(* If the domain of f is not empty, then neither is the range.                  *)
Proposition RangeIsNotEmpty : forall (f a b:U),
  Fun f a b -> a <> :0: -> range f <> :0:.
Proof.
  intros f a b H1. apply FunctionOn.RangeIsNotEmpty, H1.
Qed.

(* A function f:a -> b equals its own restriction to the domain a.              *)
Proposition IsRestrict : forall (f a b:U),
  Fun f a b -> f = f :|: a.
Proof.
  intros f a b H1. apply FunctionOn.IsRestrict, H1.
Qed.

(* Restricting a function f:a -> b to a subset c of a gives a function c -> b.  *)
Proposition Restrict : forall (f a b c:U),
  Fun f a b -> c :<=: a -> Fun (f:|:c) c b.
Proof.
  intros f a b c [H1 H2] H3. split.
  - apply FunctionOn.Restrict with a; assumption.
  - apply Incl.Tran with (range f).
    + apply Restrict.RangeIsIncl.
    + apply H2.
Qed.

(* Functions agreeing on a subset of both domains have equal restrictions to it *)
Proposition RestrictEqual : forall (f a b g c d e:U),
  Fun f a b                       ->
  Fun g c d                       ->
  e :<=: a                        ->
  e :<=: c                        ->
  (forall x, x :< e -> f!x = g!x) ->
  f:|:e = g:|:e.
Proof.
  intros f a b g c d e [H1 H2] [H3 H4].
  apply FunctionOn.RestrictEqual; assumption.
Qed.

(* A singleton function {(x,y)} with y in b is a function from {x} to b.        *)
Proposition WhenSingle : forall (x y f b:U),
  y :< b -> f = :{ :(x,y): }: -> Fun f :{x}: b.
Proof.
  intros x y f b H1 H2. split.
  - apply FunctionOn.WhenSingle with y. assumption.
  - rewrite Range.WhenSingle with x y f. 2: assumption.
    intros z H3. apply Single.Charac in H3. subst. assumption.
Qed.

(* A set is a function from the empty set to b exactly when it is empty.        *)
Proposition WhenZero : forall (f b:U),
  f = :0: <-> Fun f :0: b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros f b. split; intros H1.
  - split.
    + apply FunctionOn.WhenZero. assumption.
    + rewrite Range.WhenZero. 2: assumption. apply Empty.IsIncl.
  - destruct H1 as [[[H1 _] H2] _]. apply Empty.WhenIncl.
    (* Every member of f is an ordered pair whose first component lies in the   *)
    (* domain, so an empty domain leaves no possible members of f.              *)
    intros x H3. assert (x :< f) as H4. { assumption. }
    apply H1 in H4. destruct H4 as [y [z H4]]. subst.
    assert (y :< domain f) as H5. { apply Domain.Charac. exists z. assumption. }
    rewrite H2 in H5. apply Empty.Charac in H5. contradiction.
Qed.
