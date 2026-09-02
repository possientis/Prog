
Definition leibniz (a:Type) (x y:a) : Prop :=
    forall (P:a -> Prop), P x -> P y.


Arguments leibniz {a} _ _.

Notation "x == y" := (leibniz x y) (at level 40).


Lemma equal_refl : forall (a:Type) (x:a), x == x.
Proof. intros a x. unfold leibniz. intros P H. exact H. Qed.


Lemma equal_sym : forall (a:Type) (x y:a), x == y -> y == x.
Proof.
    intros a x y. unfold leibniz. intros H P Hy.
    remember (fun (y:a) => P y -> P x) as Q eqn:H'.
    assert (Q y) as Hq. { apply H. rewrite H'. intros Hx. exact Hx. }
    rewrite H' in Hq. apply Hq. exact Hy. 
Qed.

Lemma equal_trans : forall (a:Type) (x y z:a), x == y -> y == z -> x == z.
Proof.
    intros a x y z. unfold leibniz. intros Exy Eyz P Hx.
    apply Eyz, Exy. exact Hx.
Qed.

Lemma leibniz_is_eq : forall (a:Type) (x y:a), x = y <-> x == y.
Proof.
    intros a x y. split.
    - intros E. rewrite E. apply equal_refl.
    - intros E. remember (fun (y:a) => x = y) as Q eqn:H.
        unfold leibniz in E. apply E. rewrite H. reflexivity.
Qed.

(* setoid paper *)




 
