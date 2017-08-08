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

