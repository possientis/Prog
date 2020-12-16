Require Import Coq.Bool.Bool.

Require Import Logic.Axiom.Dec.
Require Import Logic.Axiom.Sec.
Require Import Logic.Axiom.Sat.
Require Import Logic.Axiom.Markov.

Definition Post : Type := forall (A:Prop), Sec A -> Sec (~A) -> Dec A.

(*
Lemma Markov2Post : Markov -> Post.
Proof.
    intros H1 A [f [H2 H3]] [g [H4 H5]]. remember (fun n => orb (f n) (g n)) as h eqn:E.
    assert (sig (fun n => h n = true) -> Dec A) as H6.
        { intros [n H6]. rewrite E in H6. destruct (f n) eqn:Ef; destruct (g n) eqn:Eg.
            { exfalso. assert (~A) as H7. { apply H5. exists n. assumption. }
              apply H7, H3. exists n. assumption. }
            { left. apply H3. exists n. assumption. }
            { right. apply H5. exists n. assumption. }
            { inversion H6. }}
    apply H6.          
Show.
*)
