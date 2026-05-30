Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Prod.
Require Import ZF.Set.Relation.Fun.
Require Import ZF.Set.Relation.Fun.From.
Require Import ZF.Set.Relation.Fun.From2.
Require Import ZF.Set.Relation.Map.
Require Import ZF.Notation.Eval.

(* The fork of f and g sends x to the ordered pair (f(x),g(x)).                 *)
Definition fork (c f g:U) : U := from c (fun x => :(f!x,g!x):).

(* The fork map sends a pair of maps to their fork.                             *)
Definition forkMap (c a b:U) : U :=
  from2 (map c a) (map c b) (fun f g => fork c f g).

(* The fork of maps c -> a and c -> b is a map c -> a x b.                      *)
Proposition IsFun : forall (c a b f g:U),
  Fun f c a -> Fun g c b -> Fun (fork c f g) c (a :x: b).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros c a b f g H1 H2. unfold fork. apply From.IsFun.
  intros x H3. apply Prod.Charac2. split.
  - apply Fun.IsInRange with c; assumption.
  - apply Fun.IsInRange with c; assumption.
Qed.

(* The fork map is a map from map(c,a) x map(c,b) to map(c,a x b).              *)
Proposition IsFunMap : forall (c a b:U),
  Fun (forkMap c a b) ((map c a) :x: (map c b)) (map c (a :x: b)).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros c a b. unfold forkMap. apply From2.IsFun.
  intros f g H1 H2. apply CharacMap. apply IsFun.
  - apply CharacMap. assumption.
  - apply CharacMap. assumption.
Qed.
