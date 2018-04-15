Require Import Setoids.


Record Category : Type :=
  { Arrows_     : Setoid
  ; source_     : Arrows_ ~> Arrows_
  ; target_     : Arrows_ ~> Arrows_
  ; compose_    : forall (g f:elems Arrows_), 
      apply target_ f == apply source_ g -> elems Arrows_
  ; proof_ss_   : forall (f: elems Arrows_), 
      apply source_ (apply source_ f) == apply source_ f
  ; proof_ts_   : forall (f: elems Arrows_), 
      apply target_ (apply source_ f) == apply source_ f
  ; proof_tt_   : forall (f: elems Arrows_), 
      apply target_ (apply target_ f) == apply target_ f
  ; proof_st_   : forall (f: elems Arrows_), 
      apply source_ (apply target_ f) == apply target_ f
  ; proof_src_  : forall(f g:elems Arrows_),
      forall (p: apply target_ f == apply source_ g),
      apply source_ (compose_ g f p) = apply source_ f 
  ; proof_tgt_  : forall(f g:elems Arrows_), 
      forall (p: apply target_ f == apply source_ g),
      apply target_ (compose_ g f p) = apply target_ g
  ; proof_idl_  : forall(f b:elems Arrows_), 
      forall (p: apply target_ f == apply source_ b),
      b == apply target_ f -> compose_ b f p == f
  ; proof_idr_  : forall(f a:elems Arrows_), 
      forall (p: apply target_ a == apply source_ f),
      a == apply source_ f -> compose_ f a p == f
  ; proof_asc_  : forall (f g h: elems Arrows_),
      forall (p_gf: apply target_ f == apply source_ g),
      forall (p_hg: apply target_ g == apply source_ h),
      forall (p_h_gf: apply target_ (compose_ g f p_gf) == apply source_ h),
      forall (p_hg_f: apply target_ f == apply source_ (compose_ h g p_hg)),
      compose_ h (compose_ g f p_gf) p_h_gf ==
      compose_ (compose_ h g p_hg) f p_hg_f
  ; proof_compat : forall (f f' g g':elems Arrows_),
      forall (p_gf : apply target_ f  == apply source_ g),
      forall (p_gf': apply target_ f' == apply source_ g'),
      f == f' -> g == g' -> compose_ g f p_gf = compose_ g' f' p_gf'
  }
  .

(* arrows of a category *)
Definition Arr (C:Category) : Type := elems (Arrows_ C).

(* source and target of an arrow, viewed as arrows *)
Definition source (C:Category) (f:Arr C) : Arr C := apply (source_ C) f.
Definition target (C:Category) (f:Arr C) : Arr C := apply (target_ C) f.

Arguments source {C} _.
Arguments target {C} _.

(* objects of a category *)
Inductive Obj(C:Category) : Type :=
| obj : forall (a:Arr C), source a == a -> Obj C
.

Arguments obj {C} _ _.

(* converting an object to an arrow *) 
Definition arr (C:Category) (a:Obj C) : Arr C :=
    match a with
    | obj f _   => f
    end.

Arguments arr {C} _.

(* the source of an arrow is an object *)
Lemma source_is_object : forall (C:Category) (f:Arr C), 
    source (source f) == source f.
Proof. intros C f. apply proof_ss_. Qed.

(* the target of an arrow is an object *)
Lemma target_is_object : forall (C:Category) (f:Arr C), 
    source (target f) == target f.
Proof. intros C f. apply proof_st_. Qed.

Arguments source_is_object {C} _.
Arguments target_is_object {C} _.

(* source and target of an arrow, viewed as objects *)
Definition src (C:Category) (f:Arr C) : Obj C :=
    obj (source f) (source_is_object f). 

Definition tgt (C:Category) (f:Arr C) : Obj C :=
    obj (target f) (target_is_object f).

Arguments src {C} _.
Arguments tgt {C} _.

(* homset defined as a type *)
Inductive Hom (C:Category) (a b:Obj C) : Type :=
| hom : forall (f:Arr C), (source f == arr a) -> (target f == arr b) -> Hom C a b
.

Arguments Hom {C} _ _.
Arguments hom {C} {a} {b} _ _ _.

(* converting an instance of homset to an arrow *)
Definition i (C:Category) (a b:Obj C) (f:Hom a b) : Arr C :=
    match f with
    | hom f _ _ => f
    end. 

Lemma source_of_identity : forall (C:Category) (a:Obj C), source (arr a) == arr a.
Proof. intros C [a H]. simpl. assumption. Qed.
(*
Lemma target_of_identity : forall (C:Category) (a:Obj C), target (arr a) == arr a.
Proof. intros C [a H]. simpl.

Show.
*)

(*
(* identity arrow associated with an object *)
Definition id (C:Category) (a:Obj C) : Hom a a :=
*)

