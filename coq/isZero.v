Definition isZero (n:nat) : bool :=
    match n with
    | 0   => true
    | S _ => false
    end.

Lemma test1 : isZero 0 = true.
Proof. reflexivity. Qed.


Lemma test2 : isZero 1 = false.
Proof. reflexivity. Qed.

Definition IsZero (n:nat) : Prop :=
    match n with
    | 0   => True
    | S _ => False
    end.

Lemma test3 : IsZero 0.
Proof. apply I. Qed.

Lemma test4 : ~ IsZero 1.
Proof. tauto. Qed.

Inductive IsZero' : nat -> Prop :=
| zero : IsZero' 0
.

Lemma test5 : IsZero' 0.
Proof. constructor. Qed.



