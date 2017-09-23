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

Example test_orb1 : orb true  false = true.
Proof. simpl. reflexivity. Qed. 
Example test_orb2 : orb false false = false.
Proof. simpl. reflexivity. Qed. 
Example test_orb3 : orb false true  = true.
Proof. simpl. reflexivity. Qed. 
Example test_orb4 : orb true  true  = true.
Proof. simpl. reflexivity. Qed. 

Infix "&&" := andb.
Infix "||" := orb.

Example test_orb5 : false || false || true = true.
Proof. simpl. reflexivity. Qed. 

Check true.
Check negb true.
Check negb.

Theorem negb_involutive : forall b:bool,
    negb (negb b) = b.
Proof.
    intros b. destruct b.
    - reflexivity.
    - reflexivity.
Qed.


Theorem andb_comm : forall b c:bool,
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


Theorem andb_comm' : forall b c:bool,
    andb b c = andb c b.
Proof.
    intros b c. destruct b.
    { destruct c.
        { reflexivity. }
        { reflexivity. } 
    } 
    { destruct c.
        { reflexivity. }
        { reflexivity. }
    }
Qed.


Theorem andb3_exch : forall b c d:bool,
    andb (andb b c) d = andb (andb b d) c.
Proof.
    intros b c d. destruct b.
    - destruct c.
        { destruct d.
            - reflexivity.
            - reflexivity. }
        { destruct d.
            - reflexivity.
            - reflexivity. }
    - destruct c.
        { destruct d.
            - reflexivity.
            - reflexivity. }
        { destruct d.
            - reflexivity.
            - reflexivity. }
Qed.

Theorem andb_comm'' : forall b c: bool,
    andb b c = andb c b.
Proof.
    intros [][].
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
Qed.

Theorem andb_true_elim2 : forall b c:bool,
    andb b c = true -> c = true.
Proof.
    intros b c H. destruct b.
    - exact H.
    - simpl in H. destruct c.
        + reflexivity.
        + exact H.
Qed.

Definition Id (f:bool->bool) : Prop :=
    forall x:bool, f x = x.


Theorem id_applied_twice : forall f:bool->bool,
    Id f -> forall b:bool, f (f b) = b.
Proof. 
    intros f H b. unfold Id in H. rewrite H. apply H.
Qed.


Theorem andb_eq_orb : forall b c:bool,
    andb b c = orb b c -> b = c.
Proof.
    intros [] [].
    - reflexivity.
    - intros H. simpl in H. rewrite H. reflexivity.
    - intros H. simpl in H. rewrite H. reflexivity.
    - reflexivity.
Qed.


