Require Import Axiom_ProofIrrelevance.
Require Import Cast.
Require Import Eq.
Require Import Setoids.
Require Import EqSetoids.
Require Import Category7.



Definition fw (C D:Category) (p:Arr C = Arr D) (f:Arr C) : Arr D := cast p f.
Definition bw (C D:Category) (p:Arr C = Arr D) (g:Arr D) : Arr C := cast' p g.

Arguments fw {C} {D} _ _.
Arguments bw {C} {D} _ _.

Lemma bwfw : forall (C D:Category) (p q:Arr C = Arr D) (f:Arr C), 
    bw p (fw q f) = f.
Proof. intros a b p q x. apply cast_inv_left. Qed.

Lemma fwbw : forall (C D:Category) (p q:Arr C = Arr D) (g:Arr D),
   fw p (bw q g) = g. 
Proof. intros a b p q y. apply cast_inv_right. Qed.

Definition haveSameEq (C D:Category) : Prop := forall (p:Arr C = Arr D),
    (forall (f g:Arr C), f == g -> fw p f == fw p g) /\
    (forall (f g:Arr D), f == g -> bw p f == bw p g).

Lemma same_Arrows_ : forall (C D:Category), 
    Arr C = Arr D -> haveSameEq C D -> Arrows_ C = Arrows_ D.
Proof.
    intros C D p H. destruct (H p) as [Hf Hb].
    apply sameSetoid with p.
    - apply Hf.
    - apply Hb.
Qed.



Lemma same_Arrows_' : forall (C D:Category),
    Arrows_ C = Arrows_ D -> (Arr C = Arr D) /\ haveSameEq C D.
Proof. 
    intros C D H. split.
    - unfold Arr. rewrite H. reflexivity.
    - intros p. split. 
        + intros f g E. unfold fw. unfold Arr in p. revert p.
          revert E. revert f g. unfold cast. rewrite <- H.
          intros f g E p. assert (p = eq_refl) as P.
            { apply proof_irrelevance. }
          rewrite P. assumption.
        + intros f g E. unfold bw. unfold Arr in p. revert p.
          revert E. revert f g. unfold cast', cast, eq_sym, Arr.
          rewrite <- H. intros f g E p. assert (p = eq_refl) as P.
            { apply proof_irrelevance. }
          rewrite P. assumption.
Qed.

Definition haveSameSource (C D:Category) : Prop := forall (p:Arr C = Arr D),
    forall (f: Arr C), fw p (source f) == source (fw p f).
 
