Require Import Axiom_ProofIrrelevance. 

Definition cast (a b:Type) (p: a = b) (x:a) : b :=
    match p in _ = T return T with
    | eq_refl   => x
    end.

Arguments cast {a} {b} _ _.

Definition cast_inv (a b:Type) (p: a = b) (y:b) :a :=
    cast (eq_sym p) y.


Arguments cast_inv {a} {b} _ _.

Lemma cast_proof_irrel : forall (a b:Type) (p q:a = b) (x:a),
    cast p x = cast q x.
Proof.
    intros a b p q x. assert (p = q) as E. 
    { apply proof_irrelevance. }
    rewrite E. reflexivity.
Qed.

Lemma cast_inv_left : forall (a b:Type) (p:a = b) (x:a),
    cast_inv p (cast p x) = x.
Proof.
    intros a b p x. unfold cast. unfold eq_sym.
    generalize p. revert x. rewrite <- p. clear p b. intros x p. 
    assert (p = eq_refl) as E. { apply proof_irrelevance. }
    rewrite E. reflexivity.
Qed.


Lemma cast_inv_right : forall (a b:Type) (p:a = b) (y:b), 
    cast p (cast_inv p y) = y.
Proof.
    intros a b p y. unfold cast, cast_inv, cast, eq_sym.
    generalize p. revert y. rewrite <- p. clear p b. intros x p.
    assert (p = eq_refl) as E. { apply proof_irrelevance. }
    rewrite E. reflexivity.
Qed.

 


