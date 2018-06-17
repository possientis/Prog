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

Lemma fw_is_bw : forall (C D:Category)(p:Arr C = Arr D)(q:Arr D = Arr C)(f:Arr C),
    fw p f = bw q f.
Proof.
    intros C D p q f. revert f q. generalize p. unfold Arr in p. 
    unfold fw, bw, cast, cast', eq_sym, cast, Arr. rewrite <- p. clear p.
    intros p f q. 
    assert (p = eq_refl) as P. { apply proof_irrelevance. }
    assert (q = eq_refl) as Q. { apply proof_irrelevance. }
    rewrite P, Q. reflexivity.
Qed.

Lemma bw_is_fw : forall (C D:Category)(p:Arr C = Arr D)(q:Arr D = Arr C)(f:Arr D),
    bw p f = fw q f.
Proof.
    intros C D p q f. revert f q. generalize p. unfold Arr in p. 
    unfold fw, bw, cast, cast', eq_sym, cast, Arr. rewrite <- p. clear p.
    intros p f q. 
    assert (p = eq_refl) as P. { apply proof_irrelevance. }
    assert (q = eq_refl) as Q. { apply proof_irrelevance. }
    rewrite P, Q. reflexivity.
Qed.

(*   HERE <---------------------------------------------------
Lemma fw_compose : forall (C D E:Category), 
    forall (p:Arr C = Arr D) (q:Arr D = Arr E) (r:Arr C = Arr E),
    forall (f:Arr C), fw q (fw p f) = fw r f.
Proof.

Show.
*)
 
(*

Definition haveSameEq (C D:Category) : Prop := 
    Arr C = Arr D /\
    forall (p:Arr C = Arr D),
    (forall (f g:Arr C), f == g -> fw p f == fw p g) /\
    (forall (f g:Arr D), f == g -> bw p f == bw p g).

Lemma haveSameEq_refl : forall (C:Category), haveSameEq C C.
Proof. 
    intros C. split.
    - reflexivity.
    - split; intros f g H.
        + unfold fw, cast. 
            assert (p = eq_refl) as P. { apply proof_irrelevance. }
            rewrite P. assumption.
        + unfold bw, cast. 
            assert (p = eq_refl) as P. { apply proof_irrelevance. }
            rewrite P. assumption.
Qed.


Lemma haveSameEq_sym : forall (C D:Category), haveSameEq C D -> haveSameEq D C.
Proof.
    intros C D. unfold haveSameEq. intros [p H]. split.
    - symmetry. assumption.
    - intros q. destruct (H p) as [Hf Hb]. clear H. split; intros f g E.
        + assert (fw q f = bw p f) as F. { apply fw_is_bw. }
          assert (fw q g = bw p g) as G. { apply fw_is_bw. }
          rewrite F, G. apply Hb. assumption.
        + assert (bw q f = fw p f) as F. { apply bw_is_fw. }
          assert (bw q g = fw p g) as G. { apply bw_is_fw. }
          rewrite F, G. apply Hf. assumption.
Qed.


Lemma haveSameEq_trans : forall (C D E:Category), 
    haveSameEq C D -> haveSameEq D E -> haveSameEq C E.
Proof.
    intros C D E. unfold haveSameEq. 
    intros [pCD HCD]. destruct (HCD pCD) as [HfCD HbCD]. clear HCD.
    intros [pDE HDE]. destruct (HDE pDE) as [HfDE HbDE]. clear HDE.
    split.
    - apply eq_trans with (Arr D); assumption.
    - intros pCE. split; intros f g H.
        +

Show.
      
*)
(*
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
 

Definition haveSameTarget (C D:Category) : Prop := forall (p:Arr C = Arr D),
    forall (f: Arr C), fw p (target f) == target (fw p f).

Lemma fw' : forall (C D:Category) (p:Arr C = Arr D) (f g:Arr C),
    haveSameEq C D ->
    haveSameSource C D -> 
    haveSameTarget C D ->
    target f == source g -> target (fw p f) == source (fw p g).
Proof.
    intros C D p f g E S T H. destruct (E p) as [Ef Eb]. clear E.
    apply trans with (fw p (target f)).
    - apply sym. apply T.
    - apply trans with (fw p (source g)).
        + apply Ef. assumption.
        + apply S.
Qed.       

Arguments fw' {C} {D} _ _ _ _ _ _ _.

Definition haveSameCompose (C D:Category) : Prop := 
    forall (p:Arr C = Arr D),
    forall (E:haveSameEq C D),
    forall (S:haveSameSource C D),
    forall (T:haveSameTarget C D),
    forall (f g:Arr C),
    forall (H:target f == source g),
        fw p (compose g f H) = compose (fw p g) (fw p f) (fw' p f g E S T H). 


Definition catEq (C D:Category) : Prop :=
    Arr C = Arr D       /\
    haveSameEq C D      /\
    haveSameSource C D  /\
    haveSameTarget C D  /\
    haveSameCompose C D.
*)


