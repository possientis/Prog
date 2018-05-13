Require Import Setoids.
Require Import Category7.

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

(*
Lemma fwSource : forall (C D:Category) (p:Arr C = Arr D) (f:Arr C),
    fwArr C D p (source f) == source (fwArr C D p f).
Proof.
    intros C D p f. unfold fwArr.

Show.
*)

(*
Lemma fwDefine (C D:Category) : forall (p:Arr C = Arr D) (f g:Arr C),
    target f == source g -> target (fwArr C D p f) == source (fwArr C D p g).
Proof. 
    intros p f g H. unfold fwArr.

Show.
*)

(*
Definition equalCat (C D:Category) : Prop :=
    (Arr C = Arr D) /\
    (forall (p:Arr C = Arr D) (f:Arr C), 
        source f == bwArr C D p (source (fwArr C D p f))) /\
    (forall (p:Arr C = Arr D) (f:Arr C),
        target f == bwArr C D p (target (fwArr C D p f))) /\
    (forall (p:Arr C = Arr D) (g f:Arr C) (q:target f == source g),
        compose_ C g f q == 
        bwArr C D p (compose_ D (fwArr C D p g) (fwArr C D p f) q)).
*)
