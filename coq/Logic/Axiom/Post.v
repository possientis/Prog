Require Import Coq.Bool.Bool.

Require Import Logic.Axiom.CO.
Require Import Logic.Axiom.Dec.
Require Import Logic.Axiom.Sec.
Require Import Logic.Axiom.Sat.
Require Import Logic.Axiom.Markov.
Require Import Logic.Axiom.Witness.

(* This is equivalent to Markov, see below.                                     *)
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

Lemma Post2Markov : Post -> Markov.
Proof.
    intros H1. apply MarkovSat. intros f H2.
    assert (Dec (tsat f) -> tsat f) as H3.
        { intros [H3|H3].
            { assumption. }
            { apply H2 in H3. contradiction. }}
    apply H3, H1.
        { apply exist with f. split; auto. }
        { apply exist with (fun _ => false). split; intros H4.
            { apply H2 in H4. contradiction. }
            { exfalso.  destruct H4 as [n H4]. inversion H4. }}
Qed.


Lemma MarkovDecSec : Markov -> forall (a:Type) (p:a -> Prop),
    Decidable p <-> SemiDecidable p /\ CoSemiDecidable p.
Proof.
    intros M a p. split.
    - intros [f H1]. unfold DeciderOf in H1. split.
        + exists (fun x _ => f x). intros x. split.
            { intros H2. exists 0. apply H1. assumption. }
            { intros [n H2]. apply H1. assumption. }
        + exists (fun x _ => negb (f x)). intros x. split.
            { intros H2. exists 0. destruct (f x) eqn:E.
                { exfalso. apply H2, H1. assumption. }
                { reflexivity. }}
            { intros [n H2] H3. apply H1 in H3. rewrite H3 in H2. inversion H2. }
    - intros [[F H1] [G H2]]. 
      unfold SemiDeciderOf in H1.
      unfold SemiDeciderOf in H2.
      apply pDecDecidable. intros x. apply Markov2Post in M. apply M.
        + exists (F x). apply H1.
        + exists (G x). apply H2.
Qed.

Corollary tsatNotCoSemiDecidable : Markov -> ~ CO -> ~ CoSemiDecidable (tsat).
Proof.
    intros M C H1. apply C, MarkovDecSec; try assumption.
    split; try assumption. apply tsatSemiDecidable.
Qed.

Lemma MarkovDecSecSec : Markov -> 
    forall (X:Prop), Dec X -> Sec X * Sec (~X).
Proof.
    intros M X H1. apply Markov2Post in M. split.
    - destruct H1 as [H1|H1].
        + exists (fun n => true). split; intros H2; try assumption.
          exists 0. reflexivity.
        + exists (fun n => false). split; intros H2.
            { apply H1 in H2. contradiction. }
            { destruct H2 as [n H2]. inversion H2. }
    - destruct H1 as [H1|H1].
        + exists (fun n => false). split; intros H2.
            { apply H2 in H1. contradiction. }
            { destruct H2 as [n H2]. inversion H2. }
        + exists (fun n => true). split; intros H2; try assumption.
          exists 0. reflexivity.
Defined.

Lemma MarkovSecSecDec : Markov -> 
    forall (X:Prop), Sec X * Sec (~X) -> Dec X.
Proof.
    intros M X [H1 H2]. apply Markov2Post; assumption.
Qed.

(*
Lemma MarkovSecCO : Markov ->
    (forall (X:Prop), Sec X -> Sec (~X)) -> CO.
Proof.
    intros M H1. unfold CO. apply MarkovDecSec; try assumption. split.
    - apply tsatSemiDecidable.
    - unfold CoSemiDecidable.
Show.
*)

