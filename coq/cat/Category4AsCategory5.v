Require Import Category4.
Require Import Category5.

(* given a Category4 we define the data necessary to create a Category5 *)

Definition Obj5_ (C:Category4) : Type := Obj4 C.

Definition toObj4 (C:Category4) (a:Obj5_ C) : Obj4 C := a.

Arguments toObj4 {C} _.

Inductive Hom5_ (C:Category4) (a b:Obj5_ C) : Type :=
| hom5_ : forall (f:Mor4 C), dom4 C f = a -> cod4 C f = b -> Hom5_ C a b
.

Arguments Hom5_ {C} _ _.

Arguments hom5_ {C} {a} {b} _ _ _.


Definition toMor4 (C:Category4) (a b:Obj5_ C) (f:Hom5_ a b) : Mor4 C :=
    match f with
    | hom5_ f' _ _  => f'
    end.

Arguments toMor4 {C} {a} {b} _.

Lemma toMor4_dom : forall (C:Category4) (a b:Obj5_ C) (f:Hom5_ a b),
    dom4 C (toMor4 f) = a.
Proof. intros C a b f. destruct f as [f' H1 H2]. simpl. exact H1. Qed.

Lemma toMor4_cod : forall (C:Category4) (a b:Obj5_ C) (f:Hom5_ a b),
    cod4 C (toMor4 f) = b.
Proof. intros C a b f. destruct f as [f' H1 H2]. simpl. exact H2. Qed.

Arguments toMor4_dom {C} {a} {b} _.
Arguments toMor4_cod {C} {a} {b} _.

Lemma proof_def : forall (C:Category4)(a b c:Obj5_ C)(f:Hom5_ a b)(g:Hom5_ b c),
    cod4 C (toMor4 f) = dom4 C (toMor4 g).
Proof.
    intros C a b c f g. 
    rewrite (toMor4_cod f). rewrite (toMor4_dom g). 
    reflexivity.
Qed.

Arguments proof_def {C} {a} {b} {c} _ _.

Definition comp (C:Category4) (a b c:Obj5_ C)(f:Hom5_ a b)(g:Hom5_ b c):Mor4 C :=
    compose4' (toMor4 f) (toMor4 g) (proof_def f g).

Arguments comp {C} {a} {b} {c} _ _.


Lemma comp_dom : forall (C:Category4) (a b c:Obj5_ C) (f:Hom5_ a b) (g:Hom5_ b c),
    dom4 C (comp f g) = a.
Proof.
    intros C a b c f g.
    destruct f as [f' F1 F2]. destruct g as [g' G1 G2].
    unfold comp. simpl. 
    rewrite (compose4'_dom C). exact F1. 
Qed.

Arguments comp_dom {C} {a} {b} {c} _ _.

Lemma comp_cod : forall (C:Category4) (a b c:Obj5_ C) (f:Hom5_ a b) (g:Hom5_ b c),
    cod4 C (comp f g) = c.
Proof.
    intros C a b c f g.
    destruct f as [f' F1 F2]. destruct g as [g' G1 G2].
    unfold comp. simpl. 
    rewrite (compose4'_cod C). exact G2. 
Qed.

Arguments comp_cod {C} {a} {b} {c} _ _.


Definition compose5_(C:Category4)(a b c:Obj5_ C)(f:Hom5_ a b)(g:Hom5_ b c)
    : Hom5_ a c := hom5_ (comp f g) (comp_dom f g) (comp_cod f g).

Arguments compose5_ {C} {a} {b} {c} _ _.

Definition id (C:Category4) (a:Obj5_ C) : Mor4 C := id4 C (toObj4 a).

Arguments id {C} _.

Lemma id_dom : forall (C:Category4) (a:Obj5_ C), dom4 C (id a) = a.
Proof. intros C a. unfold id. rewrite (proof_sid4 C). reflexivity. Qed.

Lemma id_cod : forall (C:Category4) (a:Obj5_ C), cod4 C (id a) = a.
Proof. intros C a. unfold id. rewrite (proof_tid4 C). reflexivity. Qed.

Arguments id_dom {C} _.
Arguments id_cod {C} _.

Definition id5_ (C:Category4) (a:Obj5_ C) : Hom5_ a a :=
    hom5_ (id a) (id_dom a) (id_cod a).

Arguments id5_ {C} _.

(*
Definition proof_idl5_ (C:Category4) : forall (a b:Obj5_ C)(f:Hom5_ a b),
    compose5_ (id5_ a) f = f. 
Proof.
    intros a b f. unfold compose5_.
Show.
*)



