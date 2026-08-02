Require Import ZF.Class.Cardinal.Aleph.
Require Import ZF.Set.Cardinal.Number.
Require Import ZF.Set.Cardinal.Regular.
Require Import ZF.Set.Core.
Require Import ZF.Set.Ordinal.Limit.
Require Import ZF.Set.Ordinal.Ordinal.
Require Import ZF.Set.Power.
Require Import ZF.Set.Relation.EvalOfClass.

Require Import ZF.Notation.Eval.


(* The set a is a weakly inaccessible cardinal.                                 *)
Definition WeaklyInaccessible (a:U) : Prop :=
  Regular a /\ exists b, Limit b /\ a = Aleph!b.

(* The set a is an inaccessible cardinal.                                       *)
Definition Inaccessible (a:U) : Prop :=
  WeaklyInaccessible a /\ forall x, card x :< a -> card :P(x) :< a.

(* A regular Aleph at a limit index is weakly inaccessible.                     *)
Proposition Charac : forall (a:U), Limit a ->
  Regular (Aleph!a) -> WeaklyInaccessible (Aleph!a).
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a H1 H2. split. 1: assumption. exists a. split; try assumption.
  reflexivity.
Qed.

(* Weak inaccessibility of Aleph(a) forces a to be a limit index.               *)
Proposition CharacRev : forall (a:U), Ordinal a ->
  WeaklyInaccessible (Aleph!a) -> Limit a /\ Regular (Aleph!a).
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a H1 H2.
  assert (Regular (Aleph!a)) as H3. { apply H2. }
  destruct H2 as [_ [b [H4 H5]]].
  assert (Ordinal b) as H6. { apply H4. }
  assert (a = b) as H7. { apply Aleph.Injective; assumption. }
  split. 2: assumption. rewrite H7. assumption.
Qed.
