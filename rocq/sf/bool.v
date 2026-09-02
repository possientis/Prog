Inductive bool  : Type :=
    | true      : bool
    | false     : bool
    .

Definition negb (b:bool) : bool :=
    match b with
    | true  => false
    | false => true
    end.

Definition andb (b1:bool)(b2:bool) : bool :=
    match b1 with
    |   true    => b2
    |   false   => false
    end.

Definition orb (b1:bool)(b2:bool) : bool :=
    match b1 with
    |   true    => true
    |   false   => b2
    end.

Infix "&&" := andb.
Infix "||" := orb.

Lemma lem_bool : forall b:bool, b = true \/ b = false.
Proof.
    destruct b.
        - left. reflexivity.
        - right. reflexivity.
Qed.


Lemma negb_involutive : forall b:bool,
    negb (negb b) = b.
Proof.
    intros b. destruct b.
    - reflexivity.
    - reflexivity.
Qed.


Lemma andb_comm : forall b c:bool,
    andb b c = andb c b.
Proof.
    intros b c. destruct b.
    - destruct c. 
        + reflexivity. 
        + reflexivity.
    - destruct c. 
        + reflexivity. 
        + reflexivity.
Qed.

Lemma orb_comm : forall b c: bool,
    orb b c = orb c b.
Proof.
    destruct b, c.    
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
Qed.



Lemma andb_true_iff : forall b c:bool,
    b && c = true <-> b = true /\ c = true.
Proof.
    intros b c. split.
    - intros H. split. 
        + destruct b eqn: H'.
            { reflexivity. }
            { inversion H. }
        + destruct c eqn: H'.
            { reflexivity. }
            { rewrite andb_comm in H. inversion H. }
    - intros [H1 H2]. rewrite H1, H2. reflexivity.
Qed.


Lemma orb_true_iff : forall b c:bool,
    b || c = true <-> b = true \/ c = true.
Proof.
    intros b c. split.
    - intros H. destruct b eqn: H'.
        + left. reflexivity.
        + right. exact H.
    - intros [H|H].
        + rewrite H. reflexivity.
        + rewrite H. rewrite orb_comm. reflexivity.
Qed.

