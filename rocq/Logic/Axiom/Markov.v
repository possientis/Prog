Require Import Logic.Axiom.Sat.

(* Markov is equivalent to Post. So some results involving Markov are in Post.  *)

(* This is equivalent to Post, see Post module.                                 *)
Definition Markov : Prop := forall (f:nat -> bool),
    ~(forall n, f n = false) -> tsat f.

Lemma MarkovSat : Markov <-> forall (f:nat -> bool), ~~tsat f -> tsat f.
Proof.
    split; intros H1 f H2.
    - apply H1. intros H3. apply H2. intros [n H4]. 
      rewrite (H3 n) in H4. inversion H4.
    - apply H1. intros H3. apply H2. intros n. destruct (f n) eqn:E.
        + exfalso. apply H3. exists n. assumption.
        + reflexivity.
Qed.

