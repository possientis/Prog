Require Import ZF.Class.Equiv.
Require Import ZF.Class.Relation.Inj.
Require Import ZF.Class.Relation.Range.
Require Import ZF.Set.Core.
Require Import ZF.Set.Diff.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Inter2.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Prod.
Require Import ZF.Set.Relation.BijectionOn.
Require Import ZF.Set.Relation.Compose.
Require Import ZF.Set.Relation.Converse.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.Fun.
Require Import ZF.Set.Relation.FunctionOn.
Require Import ZF.Set.Relation.Image.
Require Import ZF.Set.Relation.Range.
Require Import ZF.Set.Relation.Restrict.

Module CRI := ZF.Class.Relation.Inj.
Module CRR := ZF.Class.Relation.Range.

(* f is an injective function from a to b.                                      *)
Definition Inj (f a b:U) : Prop := BijectionOn f a /\ range f :<=: b.

Proposition ToClass : forall (f a b:U),
  Inj f a b <-> CRI.Inj (toClass f) (toClass a) (toClass b).
Proof.
  intros f a b. split; intros [H1 H2]; split.
  - apply BijectionOn.ToClass; assumption.
  - apply Incl.EquivCompatL with (toClass (range f)). 2: assumption.
    apply Range.ToClass.
  - apply BijectionOn.ToClass; assumption.
  - apply Incl.ToClass.
    apply Incl.EquivCompatL with (CRR.range (toClass f)). 2: assumption.
    apply Equiv.Sym, Range.ToClass.
Qed.

(* If f is an injection from a to b, then it is a function from a to b.         *)
Proposition IsFun : forall (f a b:U), Inj f a b -> Fun f a b.
Proof.
  intros f a b [H1 H2]. split. 2: assumption.
  apply BijectionOn.IsFunctionOn. assumption.
Qed.

(* Two injections with the same domains and which coincide pointwise are equal. *)
Proposition EqualCharac : forall (f a b g c d:U),
  Inj f a b                       ->
  Inj g c d                       ->
  a = c                           ->
  (forall x, x :< a -> f!x = g!x) ->
  f = g.
Proof.
  intros f a b g c d [H1 _] [H2 _]. apply BijectionOn.EqualCharac; assumption.
Qed.

Proposition ImageOfDomain : forall (f a b:U),
  Inj f a b -> f:[a]: = range f.
Proof.
  intros F A B H1. apply BijectionOn.ImageOfDomain, H1.
Qed.

(* An injection f:a -> b is a subset of axb.                                    *)
Proposition IsIncl : forall (f a b:U),
  Inj f a b -> f :<=: a :x: b.
Proof.
  intros f a b H1. apply Fun.IsIncl, IsFun. assumption.
Qed.

Proposition InvImageOfRange : forall (f a b:U),
  Inj f a b -> f^:-1::[range f]: = a.
Proof.
  intros f a b H1. apply BijectionOn.InvImageOfRange, H1.
Qed.

(* If f and g are injections then so is the composition g.f.                    *)
Proposition Compose : forall (f g a b c:U),
  Inj f a b ->
  Inj g b c ->
  Inj (g :.: f) a c.
Proof.
  intros f g a b c [H1 H2] [H3 H4]. split.
  - apply BijectionOn.Compose with b; assumption.
  - apply ZF.Set.Incl.Tran with (range g). 2: assumption.
    apply Compose.RangeIsSmaller.
Qed.

Proposition EvalCharac : forall (f a b x y:U),
  Inj f a b -> x :< a -> :(x,y): :< f <-> f!x = y.
Proof.
  intros f a b x y H1. apply BijectionOn.EvalCharac, H1.
Qed.

Proposition Satisfies : forall (f a b x:U),
  Inj f a b -> x :< a -> :(x,f!x): :< f.
Proof.
  intros f a b x H1. apply BijectionOn.Satisfies, H1.
Qed.

Proposition IsInRange : forall (f a b x:U),
  Inj f a b -> x :< a -> f!x :< b.
Proof.
  intros f a b x H1. apply Fun.IsInRange, IsFun. assumption.
Qed.

Proposition ImageCharac : forall (f a b c:U), Inj f a b ->
  forall y, y :< f:[c]: <-> exists x, x :< c /\ x :< a /\ f!x = y.
Proof.
  intros f a b c H1. apply BijectionOn.ImageCharac, H1.
Qed.

Proposition DomainOfCompose : forall (f g a b c:U),
  Inj f a b ->
  Inj g b c ->
  domain (g :.: f) = a.
Proof.
  intros f g a b c H1 H2. assert (Inj (g :.: f) a c) as H3. {
    apply Compose with b; assumption. }
  destruct H3 as [[_ H3] _]. apply H3.
Qed.

Proposition ComposeEval : forall (f g a b c x:U),
  Inj f a b ->
  Inj g b c ->
  x :< a    ->
  (g :.: f)!x = g!(f!x).
Proof.
  intros f g a b c x [H1 H2] [H3 H4] H5.
  apply BijectionOn.ComposeEval with a b; try assumption.
  apply IsInRange with a. 2: assumption. split; assumption.
Qed.

(* Characterisation of the range of f.                                          *)
Proposition RangeCharac : forall (f a b y:U),
  Inj f a b -> y :< range f <-> exists x, x :< a /\ f!x = y.
Proof.
  intros f a b y H1. apply BijectionOn.RangeCharac, H1.
Qed.

Proposition RangeIsNotEmpty : forall (f a b:U),
  Inj f a b -> a <> :0: -> range f <> :0:.
Proof.
  intros f a b H1. apply BijectionOn.RangeIsNotEmpty, H1.
Qed.

(* An injection from a to b is equal to its restriction to a.                   *)
Proposition IsRestrict : forall (f a b:U),
  Inj f a b -> f = f:|:a.
Proof.
  intros f a b H1. apply BijectionOn.IsRestrict, H1.
Qed.

Proposition Restrict : forall (f a b c:U),
  Inj f a b -> c :<=: a -> Inj (f:|:c) c b.
Proof.
  intros f a b c [H1 H2] H3. split.
  - apply BijectionOn.Restrict with a; assumption.
  - apply Incl.Tran with (range f). 2: assumption.
    apply Restrict.RangeIsIncl.
Qed.

Proposition RestrictEqual : forall (f a b g c d e:U),
  Inj f a b                       ->
  Inj g c d                       ->
  e :<=: a                        ->
  e :<=: c                        ->
  (forall x, x :< e -> f!x = g!x) ->
  f:|:e = g:|:e.
Proof.
  intros f a b g c d e [H1 H2] [H3 H4].
  apply BijectionOn.RestrictEqual; assumption.
Qed.

(* If f is an injection fron a to b with range b, f^-1 is an inj from b to a.   *)
Proposition Converse : forall (f a b:U),
  Inj f a b -> range f = b -> Inj f^:-1: b a.
Proof.
  intros f a b [H1 _] H2. split.
  - apply BijectionOn.Converse with a; assumption.
  - destruct H1 as [_ H1]. rewrite Converse.Range, H1. apply Incl.Refl.
Qed.

Proposition ConverseEvalIsInDomain : forall (f a b y:U),
  Inj f a b -> y :< range f -> f^:-1:!y :< a.
Proof.
  intros f a b y H1. apply BijectionOn.ConverseEvalIsInDomain, H1.
Qed.

Proposition ConverseEvalOfEval : forall (f a b x:U),
  Inj f a b -> x :< a -> f^:-1:!(f!x) = x.
Proof.
  intros f a b x H1. apply BijectionOn.ConverseEvalOfEval, H1.
Qed.

Proposition EvalOfConverseEval : forall (f a b y:U),
  Inj f a b -> y :< range f -> f!(f^:-1:!y) = y.
Proof.
  intros f a b y H1. apply BijectionOn.EvalOfConverseEval with a, H1.
Qed.

Proposition InvImageOfImage : forall (f a b c:U),
  Inj f a b -> c :<=: a -> f^:-1::[ f:[c]: ]: =  c.
Proof.
  intros f a b c H1. apply BijectionOn.InvImageOfImage, H1.
Qed.

Proposition ImageOfInvImage : forall (f a b c:U),
  Inj f a b -> c :<=: range f -> f:[ f^:-1::[c]: ]: =  c.
Proof.
  intros f a b c H1. apply BijectionOn.ImageOfInvImage with a, H1.
Qed.

Proposition EvalInjective : forall (f a b x y:U),
  Inj f a b -> x :< a -> y :< a -> f!x = f!y -> x = y.
Proof.
  intros f a b x y H1. apply BijectionOn.EvalInjective, H1.
Qed.

Proposition EvalInImage : forall (f a b c x:U),
  Inj f a b -> x :< a -> f!x :< f:[c]: <-> x :< c.
Proof.
  intros f a b c x H1. apply BijectionOn.EvalInImage, H1.
Qed.

Proposition Inter2Image : forall (f a b c d:U),
  Inj f a b -> f:[c :/\: d]: = f:[c]: :/\: f:[d]:.
Proof.
  intros f a b c d H1. apply BijectionOn.Inter2Image with a, H1.
Qed.

Proposition DiffImage : forall (f a b c d:U),
  Inj f a b -> f:[c :\: d]: = f:[c]: :\: f:[d]:.
Proof.
  intros f a b c d H1. apply BijectionOn.DiffImage with a, H1.
Qed.

