Require Import ZF.Class.Equiv.
Require Import ZF.Class.Ordinal.Recursion.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.FunctionOn.
Require Import ZF.Set.Relation.Restrict.
Require Import ZF.Set.Relation.RestrictOfClass.

(* The recursion set associated with the class F and set a.                     *)
(* In other words, when a is an ordinal, the unique function f                  *)
(* defined on a by the recursion: forall b :< a, f(b) = F(f|b).                 *)
Definition recursion (F:Class) (a:U) : U := (Recursion F) :|: a.

(* Low level characterisation.                                                  *)
Proposition Charac : forall (F:Class) (a x:U),
  x :< recursion F a                     <->
  exists y z f b,
    x = :(y,z):                           /\
    y :< a                                /\
    :(y,z): :< f                          /\
    Ordinal b                             /\
    FunctionOn f b                        /\
    (forall c, c :< b -> f!c = F!(f:|:c)).
Proof.
  intros F a x. split; intros H1.
  - apply RestrictOfClass.Charac in H1. 2: apply Recursion.IsFunction.
    destruct H1 as [y [z [H1 [H2 H3]]]]. destruct H3 as [f [b [H3 [H4 [H5 H6]]]]].
    exists y. exists z. exists f. exists b. split. 1: assumption.
    split. 1: assumption. split. 1: assumption. split. 1: assumption.
    split; assumption.
  - destruct H1 as [y [z [f [b [H1 [H2 [H3 [H4 [H5 H6]]]]]]]]].
    apply RestrictOfClass.CharacRev with y z; try assumption.
    + apply Recursion.IsFunction.
    + exists f. exists b. split. 1: assumption. split. 1: assumption.
      split. 1: assumption. assumption.
Qed.

Proposition Charac2 : forall (F:Class) (a y z:U),
  :(y,z):  :< recursion F a              <->
  exists f b,
    y :< a                                /\
    :(y,z): :< f                          /\
    Ordinal b                             /\
    FunctionOn f b                        /\
    (forall c, c :< b -> f!c = F!(f:|:c)).
Proof.
  intros F a y z. split; intros H1.
  - apply Charac in H1.
    destruct H1 as [y' [z' [f [b [H1 [H2 [H3 [H4 [H5 H6]]]]]]]]].
    apply OrdPair.WhenEqual in H1. destruct H1 as [H1 H7]. subst.
    exists f. exists b. split. 1: assumption. split. 1: assumption.
    split. 1: assumption. split; assumption.
  - destruct H1 as [f [b [H1 [H2 [H3 [H4 H5]]]]]]. apply Charac.
    exists y. exists z. exists f. exists b. split. 1: reflexivity.
    split. 1: assumption. split. 1: assumption. split. 1: assumption.
    split; assumption.
Qed.

Lemma RestrictRecursive : forall (F:Class) (f a b:U),
  Ordinal a                                           ->
  b :<=: a                                            ->
  FunctionOn f a                                      ->
  (forall c, c :< a -> f!c = F!(f:|:c))               ->
  (forall c, c :< b -> (f:|:b)!c = F!((f:|:b) :|: c)).
Proof.
  intros F f a b H1 H2 H3 H4 c H5.
  assert ((f:|:b)!c = f!c) as H6. {
    apply Restrict.Eval. 2: assumption. apply H3. }
  assert ((f:|:b) :|: c = f:|:c) as H7. {
    apply FunctionOn.RestrictEqual with b a. 2: assumption.
    - apply FunctionOn.Restrict with a; assumption.
Admitted.
