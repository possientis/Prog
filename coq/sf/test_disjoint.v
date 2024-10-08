Require Import list.
Require Import In.
Require Import disjoint.

Example test_nodup1 : nodup [1,2,3,4].
Proof.
    apply nodup_cons.
    - apply nodup_cons.
        + apply nodup_cons.
            { apply nodup_cons.
                { apply nodup_nil. }
                { intro H. exact H. }
            } 
            { intros [H|H].
                { inversion H. }
                { exact H. }
            }
        + intros [H|[H|H]].
            { inversion H. }
            { inversion H. }
            { exact H. }
    - intros [H|[H|[H|H]]].
        + inversion H.
        + inversion H.
        + inversion H.
        + exact H.
Qed.

Example test_nodup2 : @nodup bool [].
Proof. apply nodup_nil. Qed.

Example test_nodup3 : ~ nodup [1,2,1].
Proof.
    intros H. inversion H as [H0|l n H1 H2 H3].
    apply H2. right. left. reflexivity.
Qed.

Example test_nodup4 : ~ nodup [true,true].
Proof.
    intros H. inversion H as [H0|l b H1 H2 H3].
    apply H2. left. reflexivity.
Qed.


Example test_nostutter1 : nostutter [3,1,4,1,5,6].
Proof.
    apply nostutter_double.
    - apply nostutter_double.
        + apply nostutter_double.
            { apply nostutter_double.
                { apply nostutter_double.
                    { apply nostutter_single. }
                    { intros H. inversion H. }
                }
                { intros H. inversion H. }
            }
            { intros H. inversion H. }
        + intros H. inversion H.
    - intros H. inversion H.
Qed.


Example test_nostutter2 : nostutter (@nil nat).
Proof. apply nostutter_nil. Qed.


Example test_nostutter3 : nostutter [5].
Proof. apply nostutter_single. Qed.


(* fails on version 8.4 
Example test_nostutter4 : ~ nostutter [3,1,1,4].
Proof.
    intros H. inversion H as [x|x|x y l H0 H1 H2].
    inversion H0 as [z|z|z t k H6 H7 H8].
    apply H7. reflexivity.
Qed.
*)

