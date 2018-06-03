Require Import Cast.
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

Lemma sameArr : forall (C D:Category) (p:Arr C = Arr D),
    (forall (f g:Arr C), f == g -> fw p f == fw p g) ->
    (forall (f g:Arr D), f == g -> bw p f == bw p g) ->
    Arrows_ C = Arrows_ D. 
Proof. intros C D p Hf Hb. apply sameSetoid with p; assumption. Qed.

