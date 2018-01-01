Require Import Axiom_ProofIrrelevance.
Require Import Cast.
Require Import Category.
Require Import Eq_Category.
Require Import Category3.
Require Import Eq_Category3.
Require Import CategoryAsCategory3.
Require Import Category3AsCategory.


Theorem ToCatToCat3 : forall (A:Type) (c:Category A),
    toCategory (toCategory3 c) = c.
Proof. 
    intros A c. apply eq_Category.
    -intros f. reflexivity.
    -intros f. reflexivity.
    - intros f g. reflexivity.
Qed.


Lemma ToCat3ToCat_support : forall (c:Category3), 
    A3 (toCategory3 (toCategory c)) = A3 c.
Proof. intros c. reflexivity. Qed.

Theorem ToCat3ToCat : forall (c:Category3),
    toCategory3 (toCategory c) = c.
Proof.
    intros c. apply (eq_Category3 _ _ (ToCat3ToCat_support c)).
    - simpl. rewrite (proof_irrelevance _ (ToCat3ToCat_support c) eq_refl).
        simpl. unfold A3_, source_. reflexivity.
    - simpl. rewrite (proof_irrelevance _ (ToCat3ToCat_support c) eq_refl).
        simpl. unfold A3_, target_. reflexivity.
    - simpl. rewrite (proof_irrelevance _ (ToCat3ToCat_support c) eq_refl).
       rewrite (proof_irrelevance _ (toOption eq_refl) eq_refl). simpl.
       unfold A3_, compose_. reflexivity.
Qed.
   





