Require Import Axiom_ProofIrrelevance.
Require Import Cast.
Require Import JMEq.
Require Import Category2.
Require Import Eq_Category2.
Require Import Category4.
Require Import Eq_Category4.
Require Import Category2AsCategory4.
Require Import Category4AsCategory2.

Theorem ToCat2ToCat4 : forall (Obj Mor:Type) (c:Category2 Obj Mor),
    toCategory2 (toCategory4 c) = c.
Proof.
    intros Obj Mor c. apply eq_Category2.
    - intros f.   reflexivity.
    - intros f.   reflexivity.
    - intros a.   reflexivity.
    - intros f g. reflexivity.
Qed.


Lemma ToCat4ToCat2_Obj : forall (c:Category4),
    Obj4 (toCategory4 (toCategory2 c)) = Obj4 c.
Proof. intros c. reflexivity. Qed.

Lemma ToCat4ToCat2_Mor : forall (c:Category4),
    Mor4 (toCategory4 (toCategory2 c)) = Mor4 c.
Proof. intros c. reflexivity. Qed.

Theorem ToCat4ToCat2 : forall (c:Category4),
    toCategory4 (toCategory2 c) = c.
Proof.
    intros c. apply (eq_Category4 _ _ (ToCat4ToCat2_Obj c) (ToCat4ToCat2_Mor c)).
    - simpl.
        rewrite (proof_irrelevance _ (ToCat4ToCat2_Obj c) eq_refl).
        rewrite (proof_irrelevance _ (ToCat4ToCat2_Mor c) eq_refl).
        simpl. unfold Mor4_, dom_. reflexivity.
    - simpl.
        rewrite (proof_irrelevance _ (ToCat4ToCat2_Obj c) eq_refl).
        rewrite (proof_irrelevance _ (ToCat4ToCat2_Mor c) eq_refl).
        simpl. unfold Mor4_, cod_. reflexivity.
    - simpl.
        rewrite (proof_irrelevance _ (ToCat4ToCat2_Obj c) eq_refl).
        rewrite (proof_irrelevance _ (ToCat4ToCat2_Mor c) eq_refl).
        simpl. unfold Obj4_, id_. reflexivity.
    - simpl.
        rewrite (proof_irrelevance _ (ToCat4ToCat2_Mor c) eq_refl).
        rewrite (proof_irrelevance _ (toOption eq_refl) eq_refl).
        simpl. unfold Mor4_, compose2_. reflexivity.
Qed.
 





