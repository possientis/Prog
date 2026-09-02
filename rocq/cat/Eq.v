Require Import Axiom_ProofIrrelevance.
Require Import Axiom_Extensionality.
Require Import Axiom_PropEqual. 


Record Eq (a:Type) : Type := equality 
    { equal : a -> a -> Prop
    ; refl  : forall (x:a), equal x x
    ; sym   : forall (x y:a), equal x y -> equal y x
    ; trans : forall (x y z:a), equal x y -> equal y z -> equal x z
    }
    . 

Arguments equal {a} _ _ _.
Arguments equality {a} _ _ _ _.


Lemma sameEq : forall (a:Type) (eq1 eq2:Eq a), 
    (forall x y, equal eq1 x y <-> equal eq2 x y) -> eq1 = eq2.
Proof.
    intros a [eq1 r1 s1 t1] [eq2 r2 s2 t2] E. simpl in E. 
    assert (eq1 = eq2) as H. 
        { apply extensionality2. intros x y. apply eqProp; apply E. }
    clear E. revert r1 s1 t1 r2 s2 t2. rewrite H. 
    rename eq2 into eq. clear H eq1.
    intros r1 s1 t1 r2 s2 t2.
    assert (r1 = r2) as R. { apply proof_irrelevance. }
    assert (s1 = s2) as S. { apply proof_irrelevance. }
    assert (t1 = t2) as T. { apply proof_irrelevance. }
    rewrite R, S, T. reflexivity.
Qed.

(* default equality for any type *)
Definition defEq (a:Type) : Eq a := equality
    (@eq a)
    (@eq_refl a)
    (@eq_sym a)
    (@eq_trans a).

Arguments defEq {a}.




