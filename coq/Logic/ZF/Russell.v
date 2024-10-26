Require Import Logic.ZF.Core.
Require Import Logic.ZF.Comprehension.

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
        { apply CompP with a. rewrite <- E'. apply H2.
        }
      rewrite E in H3.
      contradiction.
    }

  (* We claim that b does belong to itself *)
  assert (b :< b) as H2.
    { rewrite E'. apply CompIn; rewrite <- E'.
      - apply Ha.
      - rewrite E. apply H1.
    }

  (* We have obtained a contradiction *)
  contradiction.
Qed.
