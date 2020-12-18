Require Import Coq.Bool.Bool.

Require Import Logic.Axiom.Dec.
Require Import Logic.Axiom.Sec.
Require Import Logic.Axiom.Sat.
Require Import Logic.Axiom.Markov.
Require Import Logic.Axiom.Witness.

Definition Post : Type := forall (A:Prop), Sec A -> Sec (~A) -> Dec A.

Lemma Markov2Post : Markov -> Post.
Proof.
    intros H1 A [f [H2 H3]] [g [H4 H5]]. 
    remember (fun n => orb (f n) (g n)) as h eqn:E.
    assert (sig (fun n => h n = true) -> Dec A) as H6.
        { intros [n H6]. rewrite E in H6. 
          destruct (f n) eqn:Ef; destruct (g n) eqn:Eg.
            { exfalso. assert (~A) as H7. { apply H5. exists n. assumption. }
              apply H7, H3. exists n. assumption. }
            { left. apply H3. exists n. assumption. }
            { right. apply H5. exists n. assumption. }
            { inversion H6. }}
    apply H6. apply witness.         
    - intros n. rewrite E. destruct (f n) eqn:Ef; destruct (g n) eqn:Eg;
      try (left; reflexivity). right. intros H7. inversion H7.
    - apply H1. intros H7.
      assert (~A) as H8.
        { intros H8. apply H2 in H8. destruct H8 as [n H8].
          specialize H7 with n. rewrite E in H7. rewrite H8 in H7.
          destruct (g n); inversion H7. }   
      assert (~~A) as H9.
        { intros H9. apply H4 in H9. destruct H9 as [n H9].
          specialize H7 with n. rewrite E in H7. rewrite H9 in H7.
          destruct (f n); inversion H7. } 
      apply H9. assumption.
Defined.

(*
Lemma Post2Markov : Post -> Markov.
Proof.
    intros H1. apply MarkovSat. intros f H2.
Show.
*)
