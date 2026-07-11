Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Monotone.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.Fun.

Require Import ZF.Notation.Eval.

Module SOM := ZF.Set.Ordinal.Monotone.


(* Predicate expressing the fact that a is cofinal with b.                      *)
Definition Cofinal (a b:U) : Prop :=
  b :<=: a                                              /\
  exists f,
    Monotone f                                          /\
    Fun f b a                                           /\
    forall c, c :< a -> exists d, d :< b /\ c :<=: f!d.

(* A set is cofinal with zero exactly when it is zero.                          *)
Proposition WhenZero : forall (a:U),
  Cofinal a :0: <-> a = :0:.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a. split; intros H1.
  - (* Any element of a would be bounded by a value indexed by zero.            *)
    apply Empty.WhenNoElem. intros c H2.
    destruct H1 as [_ [f [_ [_ H3]]]].
    assert (exists d, d :< :0: /\ c :<=: f!d) as H4. { apply H3. assumption. }
    destruct H4 as [d [H4 _]].
    apply Empty.NoElem in H4. contradiction.
  - (* For zero itself, the empty function witnesses cofinality vacuously.      *)
    subst. split.
    + apply Empty.IsIncl.
    + exists :0:.
      assert (Monotone :0:) as H1. { apply SOM.WhenZero. reflexivity. }
      assert (Fun :0: :0: :0:) as H2. { apply Fun.WhenZero. reflexivity. }
      split. 1: assumption. split. 1: assumption.
      intros c H3. exfalso. apply Empty.Charac in H3. contradiction.
Qed.


