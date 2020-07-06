(* Sets belonging to a universe U                                               *)
Definition Sets (U:Type) := U -> Prop.

Definition elem (U:Type) (x:U) (y:Sets U) : Prop := y x.

Arguments elem {U}.

Notation "x :: y" := (elem x y) : Sets_scope.

Definition emptySet (U:Type) : Sets U := (fun (x:U) => False).

Arguments emptySet {U}.

Notation "0" := emptySet : Sets_scope.

Definition inter (U:Type) (x y:Sets U) : Sets U :=
    fun (z:U) => x z /\ y z. 

Arguments inter {U}.

Notation "x /\ y" := (inter x y) 
    (at level 80, right associativity) : Sets_scope.

Definition union (U:Type) (x y:Sets U) : Sets U :=
    fun (z:U) => x z \/ y z.

Arguments union {U}.

Notation "x \/ y" := (union x y) 
    (at level 85, right associativity) : Sets_scope.


Definition comp (U:Type) (x:Sets U) : Sets U :=
    fun (z:U) => ~x z.

Arguments comp {U}.

Notation "¬ x" := (comp x) (at level 75) : Sets_scope.


Definition diff (U:Type) (x y:Sets U) : Sets U := inter x (comp y).

Arguments diff {U}.

Notation "x \\ y" := (diff x y) (at level 90, left associativity) : Sets_scope.

Open Scope Sets_scope.

Lemma notInEmpty : forall (U:Type) (x:U), ~ x :: 0.
Proof.
    unfold elem, emptySet. intros U x H.  assumption.
Qed.

Lemma interCharac : forall (U:Type) (x y:Sets U) (z:U),
    z :: (x /\ y) <-> (z :: x) /\ (z :: y).
Proof.
    unfold elem, inter. intros U x y z. split; auto.
Qed.

Lemma unionCharac : forall (U:Type) (x y:Sets U) (z:U),
    z :: (x \/ y) <-> (z :: x) \/ (z :: y).
Proof.
    unfold elem, inter. intros U x y z. split; auto.
Qed.

Lemma compCharac : forall (U:Type) (x:Sets U) (z:U),
    z :: (¬x) <-> ~ (z :: x).
Proof.
    unfold elem, comp. intros U x z. split; auto.
Qed.

Lemma diffCharac : forall (U:Type) (x y:Sets U) (z:U),
    z :: (x \\ y) <-> z :: x /\ ~ z :: y.
Proof.
    unfold elem, diff, comp, inter. intros U x y z. split; auto.
Qed.




