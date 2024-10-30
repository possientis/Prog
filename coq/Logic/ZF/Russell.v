Require Import Logic.ZF.Core.
Require Import Logic.ZF.Comprehension.
Require Import Logic.ZF.Class.

(* Let us the define the class of all sets which do not belong to themselves.   *)
Definition Ru : Class := fun x => ~x :< x.

(* Then this is a strict class                                                  *)
Proposition StrictRu : Strict Ru.
Proof.
  unfold Strict, Small, Ru. intros [a Ha].
  assert (~ a :< a) as H1.
    { intros H2. apply (Ha a); apply H2. }
  apply H1. apply Ha, H1.
Qed.

(* There exists no set containing all sets                                      *)
Proposition Russell : ~ exists a, forall x, x :< a.
Proof.
  (* Let a be a set containing all sets *)
  intros [a Ha].

  (* Consider the predicate P x = ~ x :< x *)
  remember (fun x => ~ x :< x) as P eqn:E.

  (* Consider the set b of all x in a which do not belong to themselves *)
  remember (CompSet P a) as b eqn:E'.

  (* We claim that b does not belong to itself *)
  assert (~ b :< b) as H1.
    { intro H2.
      assert (P b) as H3.
        { apply CompInP with a. rewrite <- E'. apply H2.
        }
      rewrite E in H3.
      contradiction.
    }

  (* We claim that b does belong to itself *)
  assert (b :< b) as H2.
    { rewrite E'. apply CompInAPIn; rewrite <- E'.
      - apply Ha.
      - rewrite E. apply H1.
    }

  (* We have obtained a contradiction *)
  contradiction.
Qed.
