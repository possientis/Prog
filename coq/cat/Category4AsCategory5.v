Require Import Axiom_ProofIrrelevance.
Require Import Option.
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

Lemma Hom5ToMor4 : forall (C:Category4) (a b:Obj5_ C) (f:Hom5_ a b),
    forall (p:dom4 C (toMor4 f) = a) (q:cod4 C (toMor4 f) = b), 
        hom5_ (toMor4 f) p q = f.
Proof.
    intros C a b f p q. destruct f as [f' F1 F2]. simpl.
    rewrite (proof_irrelevance _ p F1).
    rewrite (proof_irrelevance _ q F2).
    reflexivity.
Qed.


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

Lemma comp_idl : forall (C:Category4) (a b:Obj5_ C) (f:Hom5_ a b),
    comp (id5_ a) f = toMor4 f.
Proof. intros C a b f. unfold comp, id5_, id. apply compose4'_idl. Qed.

Lemma comp_idr : forall (C:Category4) (a b:Obj5_ C) (f:Hom5_ a b),
    comp f (id5_ b) = toMor4 f.
Proof. intros C a b f. unfold comp, id5_, id. apply compose4'_idr. Qed.

Definition proof_idl5_ (C:Category4) : forall (a b:Obj5_ C)(f:Hom5_ a b),
    compose5_ (id5_ a) f = f. 
Proof.
    intros a b f. unfold compose5_.
    remember (comp_dom (id5_ a) f) as p eqn:Hp.
    remember (comp_cod (id5_ a) f) as q eqn:Hq.
    clear Hp Hq. revert p q. rewrite comp_idl.
    intros p q. apply Hom5ToMor4.
Qed.

Definition proof_idr5_ (C:Category4) : forall (a b:Obj5_ C)(f:Hom5_ a b),
    compose5_ f (id5_ b) = f. 
Proof.
    intros a b f. unfold compose5_.
    remember (comp_dom f (id5_ b)) as p eqn:Hp.
    remember (comp_cod f (id5_ b)) as q eqn:Hq.
    clear Hp Hq. revert p q. rewrite comp_idr.
    intros p q. apply Hom5ToMor4.
Qed.

(*
Definition proof_asc5_ (C:Category4) : forall (a b c d:Obj5_ C),
    forall (f:Hom5_ a b) (g:Hom5_ b c) (h:Hom5_ c d),
        compose5_ (compose5_ f g) h = compose5_ f (compose5_ g h).
Proof.
    intros a b c d f g h. unfold compose5_.
    remember (comp_dom f g) as p eqn:Hp.
    remember (comp_cod f g) as q eqn:Hq.
    remember (comp_dom g h) as r eqn:Hr.
    remember (comp_cod g h) as s eqn:Hs.
    remember (comp_dom (hom5_ (comp f g) p q) h) as P eqn:HP.
    remember (comp_cod (hom5_ (comp f g) p q) h) as Q eqn:HQ.
    remember (comp_dom f (hom5_ (comp g h) r s)) as R eqn:HR.
    remember (comp_cod f (hom5_ (comp g h) r s)) as S eqn:HS.
    clear Hp Hq Hr Hs HP HQ HR HS.
    revert P Q R S.
Show.
*)
