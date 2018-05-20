Require Import Axiom_ProofIrrelevance.
Require Import Setoids.
Require Import Category7.
Require Import Eq.

Definition cast (a b:Type) (p: a = b) (x:a) : b :=
    match p in _ = T return T with
    | eq_refl   => x
    end.

Lemma switch : forall (C D:Category), Arr C = Arr D -> Arr D = Arr C.
Proof. intros C D H. symmetry. assumption. Qed.

Definition fwArr (C D:Category) (p:Arr C = Arr D) (f:Arr C) : Arr D :=
    cast (Arr C) (Arr D) p f.

Definition bwArr (C D:Category) (p:Arr C = Arr D) (f:Arr D) : Arr C :=
    cast (Arr D) (Arr C) (switch C D p) f. 

(* Equality on C and D should coincide, Arr C = Arr D as type not enough *)

(*
Lemma fwdArrCompat : forall (C D:Category) (p:Arr C = Arr D) (f g:Arr C),
    f == g -> fwArr C D p f == fwArr C D p g.
Proof.
    intros C D p f g H. unfold fwArr, cast. revert H. revert f. revert g.
    generalize p. unfold equal, eqElems.

Show.
*)

(*
Definition equalCat (C D:Category) : Prop :=
    (Arr C = Arr D) /\
    (forall (p:Arr C = Arr D) (f:Arr C), 
        fwArr C D p (source f) == source (fwArr C D p f)) /\
    (forall (p:Arr C = Arr D) (f:Arr C),
        fwArr C D p (target f) == target (fwArr C D p f)) /\
    (forall (p:Arr C = Arr D) (g f:Arr C) (q:target f == source g),
     forall (r:target (fwArr C D p f) ==  source (fwArr C D p g)),
        fwArr C D p (compose_ C g f q) == 
        compose_ D (fwArr C D p g) (fwArr C D p f) r).


Lemma reflCat : forall (C:Category), equalCat C C.
Proof. 
    intros C. split.
    - reflexivity.
    - split.
        + intros p f. unfold fwArr, source, cast.
            assert (p = eq_refl) as H. { apply proof_irrelevance. }    
            rewrite H. apply refl.
        + split. 
            { intros p f. unfold fwArr, source, cast.
                assert (p = eq_refl) as H. { apply proof_irrelevance. }    
                rewrite H. apply refl. }
            { intros p g f q r. unfold fwArr, compose, cast.
                assert (p = eq_refl) as H. { apply proof_irrelevance. }    
                revert q. revert r. rewrite H. 
                intros r. simpl in r. intros q.
                assert (q = r) as E. { apply proof_irrelevance. }
                rewrite E. apply refl. }
Qed.

Lemma symCat : forall (C D:Category), equalCat C D -> equalCat D C.
Proof.
    intros C D [eqDC [eqSRC [eqTGT eqCMP]]]. split.
    - symmetry. assumption.
    - split.
        + intros p f.

Show.
*)
