Require Import ZF.Class.Equiv.
Require Import ZF.Class.Ordinal.Induction.
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

(* The recursion set of F and a is a function defined on a, when a ordinal.     *)
Proposition IsFunctionOn : forall (F:Class) (a:U), Ordinal a ->
  FunctionOn (recursion F a) a.
Proof.
  intros F a H1. apply RestrictIsFunctionOn. assumption.
Qed.

(* The recursion set of F and a is F-recursive, when a is an ordinal.           *)
Proposition IsRecursive : forall (F:Class) (a:U), Ordinal a ->
  forall b, b :< a -> (recursion F a)!b = F!((recursion F a) :|: b).
Proof.
  intros F a H1 b H2.
  assert (b :<=: a) as H3. { apply Core.ElemIsIncl; assumption. }
  assert ((recursion F a)!b = (Recursion F)!b) as H4. {
    apply RestrictOfClass.Eval. 2: assumption. apply Recursion.IsFunctionOn. }
  assert ((recursion F a) :|: b = (Recursion F) :|: b) as H5. {
    apply FunctionOn.EqualCharac with b b. 3: reflexivity.
    - apply FunctionOn.Restrict with a. 2: assumption.
      apply IsFunctionOn. assumption.
    - apply RestrictIsFunctionOn. apply Core.IsOrdinal with a; assumption.
    - intros x H5. unfold recursion. rewrite RestrictOfClass.TowerProperty.
      + reflexivity.
      + apply Recursion.IsFunctionOn.
      + assumption. }
  rewrite H4, H5. apply Recursion.IsRecursive.
  apply Core.IsOrdinal with a; assumption.
Qed.

(* The recursion set is the unique F-recursive function defined on a.           *)
Proposition IsUnique : forall (F:Class) (a f:U),
  Ordinal a                             ->
  FunctionOn f a                        ->
  (forall b, b :< a -> f!b = F!(f:|:b)) ->
  f = recursion F a.
Proof.
  intros F a f H1 H2 H3. apply FunctionOn.EqualCharac with a a.
  1: assumption. 2: reflexivity.
  - apply IsFunctionOn. assumption.
  - remember (fun x => x :< a -> f!x = (recursion F a)!x) as A eqn:H4.
    assert (forall x, Ordinal x -> A x) as H5. {
      apply Induction'. intros b H5 H6. rewrite H4 in H6. rewrite H4.
      intros H7. rewrite H3. 2: assumption. rewrite IsRecursive; try assumption.
    assert (b :<=: a) as H8. { apply Core.ElemIsIncl; assumption. }
    assert (f:|:b = (recursion F a) :|: b) as H9. {
      apply FunctionOn.RestrictEqual with a a; try assumption.
      - apply IsFunctionOn. assumption.
      - intros x H9. apply H6. 1: assumption. apply H8. assumption. }
      rewrite H9. reflexivity. }
    intros x H6. rewrite H4 in H5. apply H5. 2: assumption.
    apply Core.IsOrdinal with a; assumption.
Qed.
