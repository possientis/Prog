Require Import ZF.Class.Equiv.
Require Import ZF.Class.Order.Rel.From.
Require Import ZF.Set.Core.
Require Import ZF.Set.Order.RestrictOfClass.
Require Import ZF.Set.OrdPair.

Module CORF := ZF.Class.Order.Rel.From.

(* Defines a set from a two variables predicate r and domain a.                 *)
Definition from (a:U) (r:U -> U -> Prop) : U := CORF.from r :/: a.


(* x is in (from a r) iff x = (y,z) with y,z in a and r y z.                    *)
Proposition Charac : forall (r:U -> U -> Prop) (a x:U),
  x :< from a r <-> exists y z, x = :(y,z): /\ y :< a /\ z :< a /\ r y z.
Proof.
  (* Proof by Claude.                                                           *)
  intros r a x. unfold from. split.
  - intros H.
    apply RestrictOfClass.Charac in H.
    destruct H as [y [z [H1 [H2 [H3 H4]]]]].
    apply CORF.Charac2 in H4.
    exists y, z. split. 1: assumption. split. 1: assumption. split; assumption.
  - intros [y [z [H1 [H2 [H3 H4]]]]].
    apply RestrictOfClass.Charac.
    exists y, z. split. 1: assumption. split. 1: assumption. split. 1: assumption.
    apply CORF.Charac2. assumption.
Qed.

(* :(x,y): is in (from a r) iff x,y are in a and r x y.                         *)
Proposition Charac2 : forall (r:U -> U -> Prop) (a x y:U),
  :(x,y): :< from a r <-> x :< a /\ y :< a /\ r x y.
Proof.
  (* Proof by Claude.                                                           *)
  intros r a x y. unfold from. split.
  - intros H.
    apply RestrictOfClass.Charac2 in H.
    destruct H as [H1 [H2 H3]].
    apply CORF.Charac2 in H3.
    split. 1: assumption. split; assumption.
  - intros [H1 [H2 H3]].
    apply RestrictOfClass.Charac2.
    split. 1: assumption. split. 1: assumption.
    apply CORF.Charac2. assumption.
Qed.


