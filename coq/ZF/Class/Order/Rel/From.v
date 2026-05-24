Require Import ZF.Class.Equiv.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.

Definition from (r:U -> U -> Prop) : Class := fun x => exists y z,
  x = :(y,z): /\ r y z.


(* :(x,y): belongs to (from r) iff r x y.                                       *)
Proposition Charac2 : forall (r:U -> U -> Prop) (x y:U),
  from r :(x,y): <-> r x y.
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)
  intros r x y. unfold from. split.
  - intros [a [b [H1 H2]]].
    apply OrdPair.Equal in H1. destruct H1 as [Ha Hb].
    subst. assumption.
  - intros H. exists x, y. split. 1: reflexivity. assumption.
Qed.

