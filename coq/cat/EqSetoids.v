Require Import Cast.
Require Import Setoids.

Definition fw (a b:Setoid) (p:elems a = elems b) (x:elems a) : elems b := cast p x.
Definition bw (a b:Setoid) (p:elems a = elems b) (y:elems b) : elems a := cast' p y.

Arguments fw {a} {b} _ _.
Arguments bw {a} {b} _ _.


Lemma fwbw : forall (a b:Setoid) (p q:elems a = elems b) (x:elems a),
    bw p (fw q x) = x.
Proof. intros a b p q x. apply cast_inv_left. Qed.

Lemma bwfw : forall (a b:Setoid) (p q:elems a = elems b) (y:elems b),
    fw p (bw q y) = y.
Proof. intros a b p q y. apply cast_inv_right. Qed.


Lemma sameSetoid : forall (a b:Setoid) (p:elems a = elems b),
    (forall (x y:elems a), x == y -> fw p x == fw p y) ->
    (forall (x y:elems b), x == y -> bw p x == bw p y) -> 
    a = b.
