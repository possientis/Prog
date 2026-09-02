Require Import not.

Lemma four_is_even : exists (n:nat), 4 = n + n.
Proof. exists 2. reflexivity. Qed.


Theorem exsists_example2 : forall (n:nat),
    (exists m, n = 4 + m) -> (exists p, n = 2 + p).
Proof. intros n [m H]. exists (2 + m). apply H. Qed.


Theorem forall_exists : forall (a:Type) (P:a -> Prop),
    (forall x, P x) -> ¬ (exists x, ¬ P x).
Proof. intros a P H [x H']. apply H'. apply H. Qed.


Theorem exists_or : forall (a:Type) (P Q:a -> Prop),
    (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
    intros a P Q. split.
    - intros [x [Hp|Hq]].
        + left. exists x. exact Hp.
        + right. exists x. exact Hq.
    - intros [[x Hp]|[x Hq]].
        + exists x. left. exact Hp.
        + exists x. right. exact Hq.
Qed.




   

