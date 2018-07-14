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

Lemma fw_compose : forall (C D E:Category), 
    forall (p:Arr C = Arr D) (q:Arr D = Arr E) (r:Arr C = Arr E),
    forall (f:Arr C), fw q (fw p f) = fw r f.
Proof.
    intros C D E p. generalize p. unfold Arr in p.
    unfold fw, cast, Arr. rewrite <- p. clear p D.
    intros p q. generalize q. rewrite <- q. clear q E.
    intros q r f.
    assert (p = eq_refl) as P. { apply proof_irrelevance. }
    assert (q = eq_refl) as Q. { apply proof_irrelevance. }
    assert (r = eq_refl) as R. { apply proof_irrelevance. }
    rewrite P, Q, R. reflexivity.
Qed.

Lemma bw_compose : forall (C D E:Category),
    forall (p:Arr C = Arr D) (q:Arr D = Arr E) (r:Arr C = Arr E),
    forall (f:Arr E), bw p (bw q f) = bw r f.
Proof.
    intros C D E p. generalize p. unfold Arr in p.
    unfold bw, cast, Arr, cast', cast, eq_sym. rewrite <- p. clear p D.
    intros p q. generalize q. rewrite <- q. clear q E.
    intros q r f.
    assert (p = eq_refl) as P. { apply proof_irrelevance. }
    assert (q = eq_refl) as Q. { apply proof_irrelevance. }
    assert (r = eq_refl) as R. { apply proof_irrelevance. }
    rewrite P, Q, R. reflexivity.
Qed.


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
        + assert (fw pDE (fw pCD f) = fw pCE f) as Hf. { apply fw_compose. }
          assert (fw pDE (fw pCD g) = fw pCE g) as Hg. { apply fw_compose. }
          rewrite <- Hf, <- Hg. apply HfDE. apply HfCD. assumption.
        + assert (bw pCD (bw pDE f) = bw pCE f) as Hf. { apply bw_compose. }
          assert (bw pCD (bw pDE g) = bw pCE g) as Hg. { apply bw_compose. }
          rewrite <- Hf, <- Hg. apply HbCD. apply HbDE. assumption.
Qed.

Lemma same_Arrows_ : forall (C D:Category), 
    haveSameEq C D -> Arrows_ C = Arrows_ D.
Proof.
    intros C D. unfold haveSameEq. intros [p H].
    destruct (H p) as [Hf Hb].
    apply sameSetoid with p.
    - apply Hf.
    - apply Hb.
Qed.


Lemma same_Arrows_' : forall (C D:Category),
    Arrows_ C = Arrows_ D -> haveSameEq C D.
Proof. 
    intros C D H. unfold haveSameEq, Arr, fw, bw, cast, cast', cast, eq_sym, Arr.
    rewrite <- H. clear H D. split.
    - reflexivity.
    - intros p. assert (p = eq_refl) as P. { apply proof_irrelevance. }
      rewrite P. split; intros f g H; assumption.
Qed.


Definition haveSameSource (C D:Category) : Prop := 
    haveSameEq C D /\
    forall (p:Arr C = Arr D),
    forall (f: Arr C), fw p (source f) == source (fw p f).

Lemma haveSameSourcefwbw : forall (C D:Category), 
    haveSameEq C D -> forall (p:Arr C = Arr D),
    (forall (f:Arr C), fw p (source f) == source (fw p f)) ->
    (forall (f:Arr D), bw p (source f) == source (bw p f)). 
Proof.
    intros C D. unfold haveSameEq. intros [p H].
    destruct (H p) as [Hf Hb]. clear H. intros q.
    assert (p = q) as E. { apply proof_irrelevance. }
    rewrite <- E. clear E q. intros H f. apply sym. 
    assert (source (bw p f) = bw p (fw p (source (bw p f)))) as E.
    { symmetry. apply bwfw. }
    rewrite E. apply Hb. clear E.
    assert (fw p (bw p f) = f) as E. { apply fwbw. }
    remember (bw p f) as g eqn:Hg. rewrite <- E. rewrite Hg.
    apply H.
Qed.

Lemma haveSameSourcebwfw : forall (C D:Category), 
    haveSameEq C D -> forall (p:Arr C = Arr D),
    (forall (f:Arr D), bw p (source f) == source (bw p f)) ->
    (forall (f:Arr C), fw p (source f) == source (fw p f)). 
Proof.
    intros C D. unfold haveSameEq. intros [p H].
    destruct (H p) as [Hf Hb]. clear H. intros q.
    assert (p = q) as E. { apply proof_irrelevance. }
    rewrite <- E. clear E q. intros H f. apply sym.  
    assert (source (fw p f) = fw p (bw p (source (fw p f)))) as E.
    { symmetry. apply fwbw. }
    rewrite E. apply Hf. clear E.
    assert (bw p (fw p f) = f) as E. { apply bwfw. }
    remember (fw p f) as g eqn:Hg. rewrite <- E. rewrite Hg.
    apply H.
Qed.



Definition haveSameTarget (C D:Category) : Prop := 
    haveSameEq C D /\
    forall (p:Arr C = Arr D),
    forall (f: Arr C), fw p (target f) == target (fw p f).

Lemma haveSameTargetfwbw : forall (C D:Category), 
    haveSameEq C D -> forall (p:Arr C = Arr D),
    (forall (f:Arr C), fw p (target f) == target (fw p f)) ->
    (forall (f:Arr D), bw p (target f) == target (bw p f)). 
Proof.
    intros C D. unfold haveSameEq. intros [p H].
    destruct (H p) as [Hf Hb]. clear H. intros q.
    assert (p = q) as E. { apply proof_irrelevance. }
    rewrite <- E. clear E q. intros H f. apply sym. 
    assert (target (bw p f) = bw p (fw p (target (bw p f)))) as E.
    { symmetry. apply bwfw. }
    rewrite E. apply Hb. clear E.
    assert (fw p (bw p f) = f) as E. { apply fwbw. }
    remember (bw p f) as g eqn:Hg. rewrite <- E. rewrite Hg.
    apply H.
Qed.

Lemma haveSameTargetbwfw : forall (C D:Category), 
    haveSameEq C D -> forall (p:Arr C = Arr D),
    (forall (f:Arr D), bw p (target f) == target (bw p f)) ->
    (forall (f:Arr C), fw p (target f) == target (fw p f)). 
Proof.
    intros C D. unfold haveSameEq. intros [p H].
    destruct (H p) as [Hf Hb]. clear H. intros q.
    assert (p = q) as E. { apply proof_irrelevance. }
    rewrite <- E. clear E q. intros H f. apply sym.  
    assert (target (fw p f) = fw p (bw p (target (fw p f)))) as E.
    { symmetry. apply fwbw. }
    rewrite E. apply Hf. clear E.
    assert (bw p (fw p f) = f) as E. { apply bwfw. }
    remember (fw p f) as g eqn:Hg. rewrite <- E. rewrite Hg.
    apply H.
Qed.


 

Lemma haveSameSource_refl : forall (C:Category), haveSameSource C C.
Proof. 
    intros C. unfold haveSameSource. split.
    - apply haveSameEq_refl.
    - intros p. assert (p = eq_refl) as P. { apply proof_irrelevance. }
        rewrite P. intros f. apply refl.
Qed.


Lemma haveSameTarget_refl : forall (C:Category), haveSameTarget C C.
Proof. 
    intros C. unfold haveSameTarget. split.
    - apply haveSameEq_refl.
    - intros p. assert (p = eq_refl) as P. { apply proof_irrelevance. }
        rewrite P. intros f. apply refl.
Qed.



Lemma haveSameSource_sym : forall (C D:Category), 
    haveSameSource C D -> haveSameSource D C.
Proof.
    intros C D. unfold haveSameSource. intros [H' H].
    unfold haveSameEq in H'. destruct H' as [p H''].
    destruct (H'' p) as [Hf Hb]. split.
    - apply haveSameEq_sym. unfold haveSameEq. split; assumption.
    - intros q f.
      assert (fw q f = bw p f) as H1. { apply fw_is_bw. }
      assert (fw q (source f) = bw p (source f)) as H2. { apply fw_is_bw. }
      rewrite H1, H2. apply haveSameSourcefwbw.
          + unfold haveSameEq. split; assumption.
          + apply H.
Qed.
 
Lemma haveSameTarget_sym : forall (C D:Category), 
    haveSameTarget C D -> haveSameTarget D C.
Proof.
    intros C D. unfold haveSameTarget. intros [H' H].
    unfold haveSameEq in H'. destruct H' as [p H''].
    destruct (H'' p) as [Hf Hb]. split.
    - apply haveSameEq_sym. unfold haveSameEq. split; assumption.
    - intros q f.
      assert (fw q f = bw p f) as H1. { apply fw_is_bw. }
      assert (fw q (target f) = bw p (target f)) as H2. { apply fw_is_bw. }
      rewrite H1, H2. apply haveSameTargetfwbw.
          + unfold haveSameEq. split; assumption.
          + apply H.
Qed.


Lemma haveSameSource_trans : forall (C D E:Category),
    haveSameSource C D -> haveSameSource D E -> haveSameSource C E.
Proof.
    intros C D E. unfold haveSameSource. 
    intros [pCD HCD] [pDE HDE]. generalize pCD, pDE.
    unfold haveSameEq in pCD. 
    destruct pCD as [qCD ECD]. destruct (ECD qCD) as [ECDf ECDb]. clear ECD.
    rename qCD into pCD. intros qCD.
    unfold haveSameEq in pDE. 
    destruct pDE as [qDE EDE]. destruct (EDE qDE) as [EDEf EDEb]. clear EDE.
    rename qDE into pDE. intros qDE.
    split. 
    - apply haveSameEq_trans with D; assumption.
    - intros pCE f.
      assert (fw pDE (fw pCD (source f)) = fw pCE (source f)) as H1.
      { apply fw_compose. }
      assert (fw pDE (fw pCD f) = fw pCE f) as H2.
      { apply fw_compose. } 
      rewrite <- H1, <- H2. 
      apply trans with (fw pDE (source (fw pCD f))).
      + apply EDEf. apply HCD.
      + apply HDE.
Qed.

Lemma haveSameTarget_trans : forall (C D E:Category),
    haveSameTarget C D -> haveSameTarget D E -> haveSameTarget C E.
Proof.
    intros C D E. unfold haveSameTarget. 
    intros [pCD HCD] [pDE HDE]. generalize pCD, pDE.
    unfold haveSameEq in pCD. 
    destruct pCD as [qCD ECD]. destruct (ECD qCD) as [ECDf ECDb]. clear ECD.
    rename qCD into pCD. intros qCD.
    unfold haveSameEq in pDE. 
    destruct pDE as [qDE EDE]. destruct (EDE qDE) as [EDEf EDEb]. clear EDE.
    rename qDE into pDE. intros qDE.
    split. 
    - apply haveSameEq_trans with D; assumption.
    - intros pCE f.
      assert (fw pDE (fw pCD (target f)) = fw pCE (target f)) as H1.
      { apply fw_compose. }
      assert (fw pDE (fw pCD f) = fw pCE f) as H2.
      { apply fw_compose. } 
      rewrite <- H1, <- H2. 
      apply trans with (fw pDE (target (fw pCD f))).
      + apply EDEf. apply HCD.
      + apply HDE.
Qed.



Lemma fw' : forall (C D:Category) (p:Arr C = Arr D) (f g:Arr C),
    haveSameSource C D -> 
    haveSameTarget C D ->
    target f == source g -> target (fw p f) == source (fw p g).
Proof.
    intros C D p f g. unfold haveSameSource, haveSameTarget.
    intros [H H1] [_ H2]. unfold haveSameEq in H.
    destruct H as [_ E]. destruct (E p) as [Hf Hb]. clear E.
    intros H. apply trans with (fw p (source g)).
    - apply trans with (fw p (target f)).
        + apply sym. apply H2.
        + apply Hf. assumption.
    - apply H1.
Qed.

Arguments fw' {C} {D} _ _ _ _ _ _.

Lemma bw' : forall (C D:Category) (p:Arr C = Arr D) (f g:Arr D),
    haveSameSource C D ->
    haveSameTarget C D ->
    target f == source g -> target (bw p f) == source (bw p g).
Proof.
    intros C D p f g. unfold haveSameSource, haveSameTarget.
    intros [H H1] [_ H2]. generalize H. intros H'.
    unfold haveSameEq in H.
    destruct H as [_ E]. destruct (E p) as [Hf Hb]. clear E.
    intros H. apply trans with (bw p (source g)).
    - apply trans with (bw p (target f)).
        + apply sym. apply haveSameTargetfwbw.
            { assumption. }
            { apply H2. }
        + apply Hb. assumption.
    - apply haveSameSourcefwbw.
        + assumption.
        + apply H1.
Qed.

Arguments bw' {C} {D} _ _ _ _ _ _.

Definition haveSameCompose (C D:Category) : Prop := 
    haveSameSource C D /\
    haveSameTarget C D /\
    forall (p:Arr C = Arr D),
    forall (S:haveSameSource C D),
    forall (T:haveSameTarget C D),
    forall (f g:Arr C),
    forall (H:target f == source g),
    forall (H': target (fw p f) == source (fw p g)),
        fw p (compose g f H) == compose (fw p g) (fw p f) H'. 


Lemma haveSameComposefwbw : forall (C D:Category),
    forall (p:Arr C = Arr D),
    forall (S:haveSameSource C D),
    forall (T:haveSameTarget C D),
        (forall (f g:Arr C),
         forall (H :target f == source g),
         forall (H': target (fw p f) == source (fw p g)),
         fw p (compose g f H) == compose (fw p g) (fw p f) H'
        )   
        -> 
        (forall (f g:Arr D),
         forall (H :target f == source g),
         forall (H':target (bw p f) == source (bw p g)),
         bw p (compose g f H) == compose (bw p g) (bw p f) H'
        ).
Proof.
    intros C D p S T. 
    generalize S. intros S'. 
    destruct S' as [[q H] S']. clear q. destruct (H p) as [Hf Hb]. clear H.
    generalize T. intros T'.
    destruct T' as [[q H] T']. clear q H.
    intros H0 f g H H'.  
    assert  ( bw p (fw p (compose (bw p g) (bw p f) H')) 
            = compose (bw p g) (bw p f) H'
            ) as E. 
        { apply bwfw. } 
    rewrite <- E. apply Hb. apply sym.
    remember (bw p f) as f' eqn:Ef.
    remember (bw p g) as g' eqn:Eg.
    assert (fw p f' = f) as Kf. { rewrite Ef. apply fwbw. }
    assert (fw p g' = g) as Kg. { rewrite Eg. apply fwbw. }
    revert H. rewrite <- Kf, <- Kg. intros H. apply H0.
Qed.

Lemma haveSameComposebwfw : forall (C D:Category),
    forall (p:Arr C = Arr D),
    forall (S:haveSameSource C D),
    forall (T:haveSameTarget C D),
        (forall (f g:Arr D),
         forall (H :target f == source g),
         forall (H':target (bw p f) == source (bw p g)),
         bw p (compose g f H) == compose (bw p g) (bw p f) H'
        )   
        ->
        (forall (f g:Arr C),
         forall (H :target f == source g),
         forall (H':target (fw p f) == source (fw p g)),
         fw p (compose g f H) == compose (fw p g) (fw p f) H'
        ). 
Proof.
    intros C D p S T. 
    generalize S. intros S'. 
    destruct S' as [[q H] S']. clear q. destruct (H p) as [Hf Hb]. clear H.
    generalize T. intros T'.
    destruct T' as [[q H] T']. clear q H.
    intros H0 f g H H'.  
    assert  ( fw p (bw p (compose (fw p g) (fw p f) H')) 
            = compose (fw p g) (fw p f) H'
            ) as E. 
        { apply fwbw. } 
    rewrite <- E. apply Hf. apply sym.
    remember (fw p f) as f' eqn:Ef.
    remember (fw p g) as g' eqn:Eg.
    assert (bw p f' = f) as Kf. { rewrite Ef. apply bwfw. }
    assert (bw p g' = g) as Kg. { rewrite Eg. apply bwfw. }
    revert H. rewrite <- Kf, <- Kg. intros H. apply H0.
Qed.


Lemma haveSameCompose_refl: forall (C:Category), haveSameCompose C C.
Proof.
    intros C. unfold haveSameCompose. split.
    - apply haveSameSource_refl.
    - split.
        + apply haveSameTarget_refl.
        + intros p S T f g H. 
          assert (p = eq_refl) as P. {apply proof_irrelevance. }
          rewrite P. simpl. intros H'.
          assert (H' = H) as P'. { apply proof_irrelevance. }
          rewrite P'. apply refl.
Qed.



Lemma haveSameCompose_sym: forall (C D:Category),
    haveSameCompose C D -> haveSameCompose D C.
Proof.
    intros C D. unfold haveSameCompose. intros [S [T H]]. split.
    - apply haveSameSource_sym. assumption.
    - split.
        + apply haveSameTarget_sym. assumption.
        + intros p' S' T' f' g' H'. generalize S. intros S0.
          destruct S0 as [S1 _]. destruct S1 as [p _].
          assert (fw p' (compose g' f' H') = bw p (compose g' f' H')) as E.
            { apply fw_is_bw. } 
          rewrite E. clear E.
          assert (fw p' f' = bw p f') as E1. { apply fw_is_bw. }
          assert (fw p' g' = bw p g') as E2. { apply fw_is_bw. }
          remember (fw' p' f' g' S' T' H') as K. clear HeqK. revert K.
          rewrite E1, E2. intros K K'.
          assert (K' = K) as E. { apply proof_irrelevance. }
          rewrite E. clear E E1 E2 K'.
          apply haveSameComposefwbw.
            { assumption. }
            { assumption. }
            { apply H.
                { assumption. }
                { assumption. }
            }
Qed.


Lemma haveSameCompose_trans: forall (C D E:Category),
    haveSameCompose C D -> haveSameCompose D E -> haveSameCompose C E.
Proof.
    intros C D E. unfold haveSameCompose. 
    intros [sCD [tCD hCD]] [sDE [tDE hDE]].
    generalize sCD. intros [[pCD eCD] _].
    generalize sDE. intros [[pDE eDE] _].
    destruct (eCD pCD) as [fCD bCD]. clear eCD.
    destruct (eDE pDE) as [fDE bDE]. clear eDE.
    split.
    - apply haveSameSource_trans with D; assumption.
    - split.
        + apply haveSameTarget_trans with D; assumption.
        + intros pCE sCE tCE f g H.
          remember (fw' pCE f g sCE tCE H) as H'. clear HeqH'. revert H'.
          assert (fw pDE (fw pCD f) = fw pCE f) as Ef. 
            { apply fw_compose. }
          assert (fw pDE (fw pCD g) = fw pCE g) as Eg. 
            { apply fw_compose. }
          assert (fw pDE (fw pCD (compose g f H)) = fw pCE (compose g f H)) as Ec.
            { apply fw_compose. }
          rewrite <- Ec, <- Ef, <- Eg. intros _ H'.
          remember (fw' pCD f g sCD tCD H) as H0 eqn:H1. clear H1.
          apply trans with (fw pDE (compose (fw pCD g) (fw pCD f) H0)).
          { apply fDE. apply hCD; assumption. }
          { apply hDE; assumption. }
Qed.

Definition catEq (C D:Category) : Prop := haveSameCompose C D.


Lemma catEq_refl : forall (C:Category), catEq C C.
Proof. intros C. apply haveSameCompose_refl. Qed.


Lemma catEq_sym : forall (C D:Category), catEq C D -> catEq D C.
Proof. intros C D H. apply haveSameCompose_sym. assumption. Qed.

Lemma catEq_trans : forall (C D E:Category), catEq C D -> catEq D E -> catEq C E.
Proof. intros C D E hCD hDE. apply haveSameCompose_trans with D; assumption. Qed.

(* This creates a universe inconsistency
Definition CatSetoid : Setoid := setoid Category catEq.
*)


