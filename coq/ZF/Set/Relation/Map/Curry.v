Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Prod.
Require Import ZF.Set.Relation.Bij.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.Fun.
Require Import ZF.Set.Relation.Fun.From.
Require Import ZF.Set.Relation.Fun.From2.
Require Import ZF.Set.Relation.Map.

(* Currying sends a function of two variables to a function-valued function.    *)
Definition curry (a b c f:U) : U :=
  from a (fun x => from b (fun y => f!:(x,y):)).

(* Uncurrying sends a function-valued function to a function of two variables.  *)
Definition uncurry (a b c g:U) : U :=
  from2 a b (fun x y => (g!x)!y).

(* The curry map sends each map on a product to its curried form.               *)
Definition curryMap (a b c:U) : U :=
  from (map (a :x: b) c) (fun f => curry a b c f).

(* The uncurry map sends each function-valued map to its uncurried form.        *)
Definition uncurryMap (a b c:U) : U :=
  from (map a (map b c)) (fun g => uncurry a b c g).

(* The curried form of a map a x b -> c is a map a -> map(b,c).                 *)
Proposition IsFun : forall (a b c f:U),
  Fun f (a :x: b) c -> Fun (curry a b c f) a (map b c).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c f H1. apply From.IsFun.
  intros x H2. apply CharacMap. apply From.IsFun.
  intros y H3. apply Fun.IsInRange with (a :x: b). 1: assumption.
  apply Prod.Charac2. split; assumption.
Qed.

(* Evaluating the curried map twice gives the original value at the pair.       *)
Proposition Eval : forall (a b c f x y:U),
  Fun f (a :x: b) c                  ->
  x :< a                             ->
  y :< b                             ->
  (curry a b c f)!x!y = f!:(x,y):.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c f x y H1 H2 H3. unfold curry.
  rewrite From.Eval. 2: assumption.
  rewrite From.Eval. 2: assumption.
  reflexivity.
Qed.

(* The curry map is a map from map(a x b,c) to map(a,map(b,c)).                 *)
Proposition IsFunMap : forall (a b c:U),
  Fun (curryMap a b c) (map (a :x: b) c) (map a (map b c)).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c. apply From.IsFun.
  intros f H1. apply CharacMap. apply IsFun. apply CharacMap. assumption.
Qed.

(* The uncurried form of a map a -> map(b,c) is a map a x b -> c.               *)
Proposition IsFunUncurry : forall (a b c g:U),
  Fun g a (map b c) -> Fun (uncurry a b c g) (a :x: b) c.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c g H1.
  apply From2.IsFun. intros x y H2 H3.
  assert (g!x :< map b c) as H4. { apply Fun.IsInRange with a; assumption. }
  apply CharacMap in H4. apply Fun.IsInRange with b; assumption.
Qed.

(* Evaluating the uncurried map at a pair gives evaluation in two steps.        *)
Proposition EvalUncurry : forall (a b c g x y:U),
  Fun g a (map b c)                           ->
  x :< a                                      ->
  y :< b                                      ->
  ((uncurry a b c g)!:(x,y):) = g!x!y.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c g x y H1 H2 H3. unfold uncurry.
  rewrite From2.Eval; try assumption. reflexivity.
Qed.

(* The uncurry map is a map from map(a,map(b,c)) to map(a x b,c).               *)
Proposition IsFunMapUncurry : forall (a b c:U),
  Fun (uncurryMap a b c) (map a (map b c)) (map (a :x: b) c).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c. apply From.IsFun.
  intros g H1. apply CharacMap. apply IsFunUncurry. apply CharacMap.
  assumption.
Qed.

(* Uncurrying after currying returns the original map on the product.           *)
Proposition FromTo : forall (a b c f:U),
  Fun f (a :x: b) c -> uncurry a b c (curry a b c f) = f.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c f H1.
  apply Fun.Equal with (a :x: b) c (a :x: b) c; try assumption.
  2: reflexivity.
  - apply IsFunUncurry. apply IsFun. assumption.
  - intros p H2. apply Prod.Charac in H2.
    destruct H2 as [x [y [H2 [H3 H4]]]]. subst p.
    assert (Fun (curry a b c f) a (map b c)) as H5. {
      apply IsFun. assumption. }
    rewrite EvalUncurry; try assumption.
    rewrite Eval; try assumption. reflexivity.
Qed.

(* Currying after uncurrying returns the original function-valued map.          *)
Proposition ToFrom : forall (a b c g:U),
  Fun g a (map b c) -> curry a b c (uncurry a b c g) = g.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c g H1.
  apply Fun.Equal with a (map b c) a (map b c); try assumption.
  2: reflexivity.
  - apply IsFun. apply IsFunUncurry. assumption.
  - intros x H2.
    assert (Fun ((curry a b c (uncurry a b c g))!x) b c) as H3. {
      apply CharacMap. apply Fun.IsInRange with a.
      - apply IsFun. apply IsFunUncurry. assumption.
      - assumption. }
    assert (Fun (g!x) b c) as H4. {
      apply CharacMap. apply Fun.IsInRange with a; assumption. }
    apply Fun.Equal with b c b c; try assumption.
    1: reflexivity.
    intros y H5.
      assert (Fun (uncurry a b c g) (a :x: b) c) as H6. {
        apply IsFunUncurry. assumption. }
      rewrite Eval; try assumption.
      rewrite EvalUncurry; try assumption. reflexivity.
Qed.

(* The curry map is a bijection between the two map spaces.                     *)
Proposition IsBijMap : forall (a b c:U),
  Bij (curryMap a b c) (map (a :x: b) c) (map a (map b c)).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c. apply From.IsBij.
  - intros f H1. apply CharacMap. apply IsFun. apply CharacMap. assumption.
  - intros f g H1 H2 H3.
    assert (Fun f (a :x: b) c) as H4. { apply CharacMap. assumption. }
    assert (Fun g (a :x: b) c) as H5. { apply CharacMap. assumption. }
    rewrite <- (FromTo a b c f). 2: assumption.
    rewrite <- (FromTo a b c g). 2: assumption.
    rewrite H3. reflexivity.
  - intros g H1. exists (uncurry a b c g). split.
    + apply CharacMap. apply IsFunUncurry. apply CharacMap. assumption.
    + apply ToFrom. apply CharacMap. assumption.
Qed.

