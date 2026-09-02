Require Import Setoids.
Require Import Category7.
Require Import Functor.

Definition functorEq (C D:Category) (F G:Functor C D) : Prop :=
    forall (a b:Obj C) (f:Hom a b), i (F <$> f) == i (G <$> f).

Arguments functorEq {C} {D} _ _.

Definition functorEq' (C D:Category) (F G:Functor C D) : Prop :=
    forall (f:Arr C), Func_ F f == Func_ G f.

Arguments functorEq' {C} {D} _ _.

(*
Lemma functorEqEq' : forall (C D:Category) (F G:Functor C D),
    functorEq F G -> functorEq' F G.
Proof.
    intros C D [F Fe Fs Ft Fc] [G Ge Gs Gt Gc] H. unfold functorEq'. 
    intros f. unfold functorEq in H. simpl. 
    unfold lift in H. unfold i in H. unfold lift_arrow_ in H.
    simpl in H.

Show.
*)    
