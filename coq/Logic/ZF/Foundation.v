Require Import Logic.ZF.Core.
Require Import Logic.ZF.Empty.
Require Import Logic.ZF.Intersect.
Require Import Logic.ZF.Singleton.

(* Every non-empty set a has an element which does not contain any element of a.*)
Axiom Foundation : forall (a:U),
  ~ a = :0: -> exists x, x :< a /\ x :/\: a = :0:.

(* No set belongs to itself.                                                    *)
Proposition NoElemLoop1 : forall x, ~ x :< x.
Proof.
  (* Let a be a set which belongs to itself *)
  intros a Ha.

  (* Consider the singleton set b = {a} *)
  remember :{a}: as b eqn:Hb.

  (* Then b is an non-empty set. *)
  assert (~ b = :0:) as H1. { rewrite Hb. apply SingleNotEmpty. }

  (* From the foundation axiom, b has an element x such that x /\ b = 0 *)
  remember (Foundation b H1) as H2 eqn:A. clear A. destruct H2 as [x [H2 H3]].

  (* So x belongs to b *)
  assert (x :< b) as A. { apply H2. } clear A.

  (* And x /\ b = 0 *)
  assert (x :/\: b = :0:) as A. { apply H3. } clear A.

  (* Since x belongs to b = {a} we have x = a *)
  assert (x = a) as H4. { rewrite Hb in H2. apply SingleCharac in H2. apply H2. }

  (* Hence we have a /\ {a} = 0 *)
  subst. assert (a :/\: :{a}: = :0:) as A. { apply H3. } clear A.

  (* And since a :< a we see that a belongs to a /\ {a}, and so it belongs to 0 *)
  assert (a :< :0:) as H4.
    { rewrite <- H3. apply IntersectCharac. split.
      - apply Ha.
      - apply SingleIn.
    }

  (* This is our desired contradiction *)
  apply EmptyCharac in H4. contradiction.
Qed.
