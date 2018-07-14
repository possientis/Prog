Require Import bool.
Require Import nat. 
Require Import hsyntax.
Require Import heval.
Require Import dictionary.
Require Import state.

Definition aequiv (a1 a2:aexp) : Prop :=
  forall (e:State), aeval e a1 = aeval e a2.

Definition bequiv (b1 b2:bexp) : Prop :=
  forall (e:State), beval e b1 = beval e b2.

Definition cequiv (c1 c2:com)  : Prop :=
  forall (e e':State), ceval c1 e e' <-> ceval c2 e e'. 


Definition pXY := HAVOC x;; HAVOC y.
Definition pYX := HAVOC y;; HAVOC x.
Definition pCopy := HAVOC x;; y ::= AKey x.


Theorem cequiv_pXY_pYX : cequiv pXY pYX.
Proof.
    intros e e'. split.
    - intros H. remember pXY as c eqn:C. revert C. 
      destruct H; intros H'; inversion H'; subst.
      + unfold pYX.
        assert (exists n, e' = t_update e x n) as H1.
            { apply ceval_havoc. assumption. }
        assert (exists m, e'' = t_update e' y m) as H2.
            { apply ceval_havoc. assumption. }
        destruct H1 as [n H1].
        destruct H2 as [m H2].
        remember (t_update e  y m) as e1 eqn:E1.
        remember (t_update e1 x n) as e2 eqn:E2.
        apply E_Seq with e1.
            { rewrite E1. constructor. }
            { assert (e'' = e2) as E.
                { rewrite H2, H1, E2, E1. apply t_update_permute.
                  intros X. inversion X.
                }
              rewrite E, E2. constructor.
            }
    - intros H. remember pYX as c eqn:C. revert C.
      destruct H; intros H'; inversion H'; subst.
      + unfold pXY.
        assert (exists m, e' = t_update e y m) as H1.
            { apply ceval_havoc. assumption. }
        assert (exists n, e'' = t_update e' x n) as H2.
            { apply ceval_havoc. assumption. }
        destruct H1 as [m H1].
        destruct H2 as [n H2].
        remember (t_update e  x n) as e1 eqn:E1.
        remember (t_update e1 y m) as e2 eqn:E2.
        apply E_Seq with e1.
            { rewrite E1. constructor. }
            { assert (e'' = e2) as E.
                { rewrite H2, H1, E2, E1. apply t_update_permute.
                  intros X. inversion X.
                }
              rewrite E, E2. constructor.
            } 
Qed.

(*
Theorem not_cequiv_pXY_pCopy : ~cequiv pXY pCopy.
Proof.
    intros H. unfold cequiv in H.
    remember emptyState as e0 eqn:E0.
    remember (t_update e0 x 0) as e1 eqn:E1.
    remember (t_update e1 y 1) as e2 eqn:E2.
    destruct (H e0 e2) as [H0 _]. clear H. rename H0 into H.
    assert (ceval pXY e0 e2) as H1.
        { unfold pXY. apply E_Seq with e1.
            { rewrite E1. constructor. }
            { rewrite E2. constructor. }
        }
    apply H in H1. clear H. rename H1 into H.
Show.
*)
