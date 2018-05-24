Record Eq (a:Type) : Type := equality 
    { equal : a -> a -> Prop
    ; refl  : forall (x:a), equal x x
    ; sym   : forall (x y:a), equal x y -> equal y x
    ; trans : forall (x y z:a), equal x y -> equal y z -> equal x z
    }
    . 

Arguments equal {a} _ _ _.
Arguments equality {a} _ _ _ _.

(* default equality for any type *)
Definition defEq (a:Type) : Eq a := equality
    (@eq a)
    (@eq_refl a)
    (@eq_sym a)
    (@eq_trans a).

Arguments defEq {a}.

(* when are two equality implementations equal ? *)


Definition equalEq (a:Type) (eq1:Eq a) (eq2:Eq a) : Prop :=
    forall (x y:a), equal eq1 x y <-> equal eq2 x y.

Arguments equalEq {a} _ _.

Lemma reflEq : forall (a:Type) (eq:Eq a), equalEq eq eq.
Proof. intros a eq x y. split; intros; assumption. Qed.

Lemma symEq : forall (a:Type) (eq1 eq2:Eq a), 
    equalEq eq1 eq2 -> equalEq eq2 eq1.
Proof. intros a eq1 eq2. unfold equalEq. intros H x y. split; apply H. Qed.

Lemma transEq : forall (a:Type) (eq1 eq2 eq3:Eq a), 
    equalEq eq1 eq2 -> equalEq eq2 eq3 -> equalEq eq1 eq3.
Proof.
    intros a eq1 eq2 eq3 H12 H23 x y. split; intros.
    - apply H23, H12. assumption.
    - apply H12, H23. assumption.
Qed.

Definition eqEq (a:Type) : Eq (Eq a) := equality
    (@equalEq   a)
    (@reflEq    a)
    (@symEq     a)
    (@transEq   a).







