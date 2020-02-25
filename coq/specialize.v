Variable a:Set.
Variable Q:Prop -> Prop.

Lemma L1 : (forall (x:a) (p:Prop), Q p) <-> forall (p:a -> Prop) (x:a), Q (p x).
Proof.
    split.
    - intros H p x. apply H. assumption.
    - intros H x p.  apply (H (fun x => p)). assumption.
Qed.

Lemma L2 : (forall (x y:a) (p:Prop), Q p) <-> forall (p:a -> a -> Prop) (x y:a), Q (p x y).
Proof.
    split. 
    - intros H p x y. apply H; assumption.
    - intros H x y p. apply (H (fun x y => p)); assumption.
Qed.

Lemma L3 : (forall (x:a), False) -> False.
Proof.
    intros H. 
    
Abort. (* Cannot be proven *) 

(* However *)
Lemma L4 : forall (y:a), (forall (x:a), False) -> False.
Proof.
    intros y H. apply H. assumption.
Qed.


