Require Import Category7.
Require Import Setoids.

Definition cast (a b:Type) (p: a = b) (x:a) : b :=
    match p in _ = T return T with
    | eq_refl   => x
    end.

Lemma switch : forall (C D:Category), Arr C = Arr D -> Arr D = Arr C.
Proof. intros C D H. symmetry. assumption. Qed.


Definition equalCat (C D:Category) : Prop :=
    (Arr C = Arr D) /\
    forall (p:Arr C = Arr D) (f:Arr C), source f == 
        cast (Arr D) (Arr C) (switch C D p) (source (cast (Arr C) (Arr D) p f)).
