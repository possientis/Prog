Require Import ZF.Class.Equiv.
Require Import ZF.Class.Relation.Bij.
Require Import ZF.Class.Relation.Range.
Require Import ZF.Set.Core.
Require Import ZF.Set.Diff.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Inter2.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Prod.
Require Import ZF.Set.Relation.Bijection.
Require Import ZF.Set.Relation.BijectionOn.
Require Import ZF.Set.Relation.Compose.
Require Import ZF.Set.Relation.Converse.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.Fun.
Require Import ZF.Set.Relation.FunctionOn.
Require Import ZF.Set.Relation.Image.
Require Import ZF.Set.Relation.Inj.
Require Import ZF.Set.Relation.OneToOne.
Require Import ZF.Set.Relation.Onto.
Require Import ZF.Set.Relation.Range.
Require Import ZF.Set.Relation.Restrict.

Module CRB := ZF.Class.Relation.Bij.
Module CRR := ZF.Class.Relation.Range.

(* f is a bijection from a to b.                                                *)
Definition Bij (f a b:U) : Prop := BijectionOn f a /\ range f = b.

(* If the set is a bijection from a to b, then so is the class.                 *)
Proposition ToClass : forall (f a b:U),
  Bij f a b -> CRB.Bij (toClass f) (toClass a) (toClass b).
Proof.
  intros f a b [H1 H2]. split.
  - apply BijectionOn.ToClass. assumption.
  - rewrite <- H2. apply Equiv.Sym, Range.ToClass.
Qed.

(* If the class is a bijection from a to b, then so is the set.                 *)
Proposition FromClass : forall (f a b:U),
  CRB.Bij (toClass f) (toClass a) (toClass b) -> Bij f a b.
Proof.
  intros f a b [H1 H2]. split.
  - apply BijectionOn.FromClass. assumption.
  - apply Equiv.EqualToClass.
    apply Equiv.EquivCompatL with (CRR.range (toClass f)). 2: assumption.
    apply Equiv.Sym, Range.ToClass.
Qed.

(* A one-to-one function whose range covers b is a bijection from a to b.       *)
Proposition FromFun : forall (f a b:U),
  Fun f a b -> OneToOne f -> b :<=: range f -> Bij f a b.
Proof.
  intros f a b H1 H2 H3.
  assert (range f = b) as H4. {
    apply Incl.Double. split. 2: assumption. apply H1. }
  assert (Bijection f) as H5. { split. 2: assumption. apply H1. }
  assert (BijectionOn f a) as H6. { split. 1: assumption. apply H1. }
  split; assumption.
Qed.

Proposition FromInj : forall (f a b:U),
  Inj f a b -> Bij f a f:[a]:.
Proof.
  intros f a b H1. split.
  - apply H1.
  - assert (domain f = a) as H2. { apply H1. }
    rewrite <- H2. symmetry. apply Range.ImageOfDomain.
Qed.

(* A bijection from a to b is a function from a to b.                           *)
Proposition IsFun : forall (f a b:U),
  Bij f a b -> Fun f a b.
Proof.
  intros f a b [H1 H2]. apply BijectionOn.IsFunctionOn in H1.
  split. 1: assumption. subst. apply Incl.Refl.
Qed.

(* A bijection from a to b is an injection from a to b.                         *)
Proposition IsInj : forall (f a b:U),
  Bij f a b -> Inj f a b.
Proof.
  intros f a b [H1 H2]. split. 1: apply H1. subst. apply Incl.Refl.
Qed.

(* A bijection from a to b is a surjection from a to b.                         *)
Proposition IsOnto : forall (f a b:U),
  Bij f a b -> Onto f a b.
Proof.
  intros f a b H1. split. 2: apply H1. apply BijectionOn.IsFunctionOn, H1.
Qed.

(* Two bijections with the same domains and which coincide pointwise are equal. *)
Proposition Equal : forall (f a b g c d:U),
  Bij f a b                       ->
  Bij g c d                       ->
  a = c                           ->
  (forall x, x :< a -> f!x = g!x) ->
  f = g.
Proof.
  intros f a b g c d [H1 _] [H2i _]. apply BijectionOn.Equal; assumption.
Qed.

(* The image of the domain a under a bijection f:a -> b equals b.               *)
Proposition ImageOfDomain : forall (f a b:U),
  Bij f a b -> f:[a]: = b.
Proof.
  intros f a b [H1 H2]. subst. apply BijectionOn.ImageOfDomain. assumption.
Qed.

(* A bijection f:a -> b is a subset of a x b.                                   *)
Proposition IsIncl : forall (f a b:U),
  Bij f a b -> f :<=: a :x: b.
Proof.
  intros f a b H1. apply Fun.IsIncl, IsFun. assumption.
Qed.

(* The inverse image of b under a bijection f:a -> b equals the domain a.       *)
Proposition InvImageOfRange : forall (f a b:U),
  Bij f a b -> f^:-1::[b]: = a.
Proof.
  intros f a b [H1 H2]. subst. apply BijectionOn.InvImageOfRange. assumption.
Qed.

(* The composition of bijections f:a -> b and g:b -> c is a bijection a -> c.   *)
Proposition Compose : forall (f g a b c:U),
  Bij f a b -> Bij g b c -> Bij (g :.: f) a c.
Proof.
  intros f g a b c [H1 H2] [H3 H4]. split.
  - apply BijectionOn.Compose with b; try assumption. subst. apply Incl.Refl.
  - subst. apply Compose.RangeIsSame. destruct H3 as [_ H3].
    rewrite H3. apply Incl.Refl.
Qed.

(* For a bijection f:a -> b and x in a, the pair (x,y) lies in f iff f!x = y.   *)
Proposition Eval' : forall (f a b x y:U),
  Bij f a b-> x :< a -> :(x,y): :< f <-> f!x = y.
Proof.
  intros f a b x y H1. apply IsFun in H1. apply Fun.Eval' with b. assumption.
Qed.

(* If (x,y) belongs to a bijection f:a -> b then f!x = y.                       *)
Proposition Eval : forall (f a b x y:U),
  Bij f a b -> :(x,y): :< f -> f!x = y.
Proof.
  intros f a b x y H1 H2. apply Eval' with a b; try assumption.
  assert (domain f = a) as H3. { apply H1. }
  rewrite <- H3. apply Domain.Charac. exists y. assumption.
Qed.

(* For a bijection f:a -> b and x in a, the pair (x,f!x) lies in f.             *)
Proposition Satisfies : forall (f a b x:U),
  Bij f a b -> x :< a -> :(x,f!x): :< f.
Proof.
  intros f a b x H1. apply IsFun in H1. apply Fun.Satisfies with b. assumption.
Qed.

(* For a bijection f:a -> b and x in a, the value f!x lies in b.                *)
Proposition IsInRange : forall (f a b x:U),
  Bij f a b -> x :< a -> f!x :< b.
Proof.
  intros f a b x H1. apply IsFun in H1. apply Fun.IsInRange. assumption.
Qed.

(* y lies in the image f[c] iff y = f!x for some x in c and in a.               *)
Proposition ImageCharac : forall (f a b c:U), Bij f a b ->
  forall y, y :< f:[c]: <-> exists x, x :< c /\ x :< a /\ f!x = y.
Proof.
  intros f a b c H1. apply BijectionOn.ImageCharac, H1.
Qed.

(* The domain of the composition of bijections f:a -> b and g:b -> c is a.      *)
Proposition DomainOfCompose : forall (f g a b c:U),
  Bij f a b             ->
  Bij g b c             ->
  domain (g :.: f) = a.
Proof.
  intros f g a b c H1 H2.
  apply Fun.DomainOfCompose with b c; apply IsFun; assumption.
Qed.

(* For bijections f:a -> b and g:b -> c, (g.f)!x = g!(f!x) for x in a.          *)
Proposition ComposeEval : forall (f g a b c x:U),
  Bij f a b               ->
  Bij g b c               ->
  x :< a                  ->
  (g :.: f)!x = g!(f!x).
Proof.
  intros f g a b c x H1 H2.
  apply Fun.ComposeEval with b c; apply IsFun; assumption.
Qed.

(* Characterisation of the range of f.                                          *)
Proposition RangeCharac : forall (f a b y:U),
  Bij f a b -> y :< b <-> exists x, x :< a /\ f!x = y.
Proof.
  intros f a b y [H1 H2]. subst. apply BijectionOn.RangeCharac. assumption.
Qed.

(* If the domain a of a bijection f:a -> b is not empty, then neither is b.     *)
Proposition RangeIsNotEmpty : forall (f a b:U),
  Bij f a b -> a <> :0: -> b <> :0:.
Proof.
  intros f a b H1. apply Onto.RangeIsNotEmpty with f, IsOnto. assumption.
Qed.

(* A bijection f:a -> b equals its own restriction to the domain a.             *)
Proposition IsRestrict : forall (f a b:U),
  Bij f a b -> f = f :|: a.
Proof.
  intros f a b H1. apply BijectionOn.IsRestrict, H1.
Qed.

(* Restricting a bijection f:a -> b to c subset a gives a bijection c -> f[c].  *)
Proposition Restrict : forall (f a b c:U),
  Bij f a b -> c :<=: a -> Bij (f:|:c) c f:[c]:.
Proof.
  intros f a b c [H1 H2] H3. split.
  - apply BijectionOn.Restrict with a; assumption.
  - apply Restrict.RangeOf.
Qed.

Proposition RestrictEqual : forall (f a b g c d e:U),
  Bij f a b                       ->
  Bij g c d                       ->
  e :<=: a                        ->
  e :<=: c                        ->
  (forall x, x :< e -> f!x = g!x) ->
  f:|:e = g:|:e.
Proof.
  intros f a b g c d e [H1 _] [H2 _]. apply BijectionOn.RestrictEqual; assumption.
Qed.

(* The converse of a bijection f:a -> b is a bijection from b to a.             *)
Proposition Converse : forall (f a b:U),
  Bij f a b -> Bij f^:-1: b a.
Proof.
  intros f a b [H1 H2]. split.
  - apply BijectionOn.Converse with a; assumption.
  - destruct H1 as [_ H1]. subst. apply Converse.Range.
Qed.

(* For a bijection f:a -> b and y in b, the value f^-1!y lies in a.             *)
Proposition ConverseEvalIsInDomain : forall (f a b y:U),
  Bij f a b -> y :< b -> f^:-1:!y :< a.
Proof.
  intros f a b y H1 H2. apply IsInRange with b. 2: assumption.
  apply Converse. assumption.
Qed.

(* For a bijection f:a -> b and x in a, applying f^-1 after f recovers x.       *)
Proposition ConverseEvalOfEval : forall (f a b x:U),
  Bij f a b -> x :< a -> f^:-1:!(f!x) = x.
Proof.
  intros f a b x H1. apply BijectionOn.ConverseEvalOfEval, H1.
Qed.

(* For a bijection f:a -> b and y in b, applying f after f^-1 recovers y.       *)
Proposition EvalOfConverseEval : forall (f a b y:U),
  Bij f a b -> y :< b -> f!(f^:-1:!y) = y.
Proof.
  intros f a b y [H1 H2] H3. subst.
  apply BijectionOn.EvalOfConverseEval with a; assumption.
Qed.

(* For a bijection f:a -> b and c subset a, the inverse image of f[c] is c.     *)
Proposition InvImageOfImage : forall (f a b c:U),
  Bij f a b -> c :<=: a -> f^:-1::[ f:[c]: ]: = c.
Proof.
  intros f a b c [H1 H2] H3. apply BijectionOn.InvImageOfImage with a; assumption.
Qed.

(* For a bijection f:a -> b and c subset b, the image of the inverse image is c.*)
Proposition ImageOfInvImage : forall (f a b c:U),
  Bij f a b -> c :<=: b -> f:[ f^:-1::[c]: ]: = c.
Proof.
  intros f a b c [H1 H2] H3.
  subst. apply BijectionOn.ImageOfInvImage with a; assumption.
Qed.

(* A bijection f:a -> b is injective: equal values in b imply equal inputs.     *)
Proposition EvalInjective : forall (f a b x y:U),
  Bij f a b -> x :< a -> y :< a -> f!x = f!y -> x = y.
Proof.
  intros f a b x y H1. apply BijectionOn.EvalInjective, H1.
Qed.

(* For a bijection f:a -> b and x in a, f!x lies in f[c] iff x lies in c.       *)
Proposition EvalInImage : forall (f a b c x:U),
  Bij f a b -> x :< a -> f!x :< f:[c]: <-> x :< c.
Proof.
  intros f a b c x H1. apply BijectionOn.EvalInImage, H1.
Qed.

(* A bijection preserves binary intersections: f[c /\ d] = f[c] /\ f[d].        *)
Proposition Inter2Image : forall (f a b c d:U),
  Bij f a b -> f:[c :/\: d]: = f:[c]: :/\: f:[d]:.
Proof.
  intros f a b c d H1. apply BijectionOn.Inter2Image with a, H1.
Qed.

(* A bijection preserves set differences: f[c \ d] = f[c] \ f[d].               *)
Proposition DiffImage : forall (f a b c d:U),
  Bij f a b -> f:[c :\: d]: = f:[c]: :\: f:[d]:.
Proof.
  intros f a b c d H1. apply BijectionOn.DiffImage with a, H1.
Qed.

