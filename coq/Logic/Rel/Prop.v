Lemma equivRelf : forall (A:Prop), A <-> A.
Proof.
    intro A. split; auto.
Qed.


Lemma equivSym : forall (A B:Prop), A <-> B -> B <-> A.
Proof.
    intros A B [H1 H2]. split; assumption.
Qed.


Lemma equivTrans : forall (A B C:Prop), A <-> B -> B <-> C -> A <-> C.
Proof.
    intros A B C [H1 H2] [H3 H4]. split; intros H5.
    - apply H3, H1. assumption.
    - apply H2, H4. assumption.
Qed.

Lemma implyCompatL : forall (A A' B:Prop), 
    (A <-> A') -> 
    ((A -> B) <-> (A' -> B)).
Proof.
    intros A A' B [H1 H2]. split; intros H3 H4; apply H3.
    - apply H2. assumption.
    - apply H1. assumption.
Qed.

Lemma implyCompatR : forall (A B B':Prop),
    (B <-> B') -> 
    ((A -> B) <-> (A -> B')).
Proof.
    intros A B B' [H1 H2]. split; intros H3 H4.
    - apply H1, H3. assumption.
    - apply H2, H3. assumption.
Qed.

Lemma implyCompatLR : forall (A A' B B':Prop),
    (A <-> A') ->
    (B <-> B') ->
    ((A -> B) <-> (A' -> B')).
Proof.
    intros A A' B B' H1 H2. apply equivTrans with (A' -> B).
    - apply implyCompatL. assumption.
    - apply implyCompatR. assumption.
Qed.

Lemma allCompat : forall (a:Type) (A B:a -> Prop), 
  (forall (x:a), A x <-> B x) ->
  ((forall (x:a), A x) <-> (forall (x:a), B x)).
Proof.
  intros a A B H1. 
  split; intros H2 x; specialize H1 with x; destruct H1 as [H1 H3]. 
  - apply H1, H2.
  - apply H3, H2.
Qed.
