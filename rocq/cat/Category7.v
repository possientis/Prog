Require Import Setoids.

Declare Scope categ.

(* The internals of a category are not readable, however the hope 
   is to provide a highly intuitive API to categorical notions.
   A category is defined as a base Setoid 'Arrows_' (i.e. a type 
   with equality) which represents the class of all arrows of the 
   category. On 'Arrows_' are defined two unary operations 'source_'
   and 'target_' as well as a partial binary operation 'compose_'.
   The objects of the category are not given by additional data, but
   are simply identified with identity arrows. An object of the  
   category is simply any arrow whose 'source_' is itself, (in
   which case its target is also itself). The main advantage of
   identifying objects with identity arrows, is that we do not 
   need to provide a seperate equality primitive for objects.
*)
     

Record Category : Type := category
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
      apply source_ (compose_ g f p) == apply source_ f 
  ; proof_tgt_  : forall(f g:elems Arrows_), 
      forall (p: apply target_ f == apply source_ g),
      apply target_ (compose_ g f p) == apply target_ g
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
  ; proof_compat_ : forall (f f' g g':elems Arrows_),
      forall (p_gf : apply target_ f  == apply source_ g),
      forall (p_gf': apply target_ f' == apply source_ g'),
      f == f' -> g == g' -> compose_ g f p_gf == compose_ g' f' p_gf'
  }
  .

(* arrows of a category *)
Definition Arr (C:Category) : Type := elems (Arrows_ C).

(* source and target of an arrow, viewed as arrows *)
Definition source  (C:Category) (f:Arr C) : Arr C := apply (source_ C) f.
Definition target  (C:Category) (f:Arr C) : Arr C := apply (target_ C) f.

Arguments source {C} _.
Arguments target {C} _.

Definition compose (C:Category) (g f:Arr C) (p:target f == source g) : Arr C :=
    compose_ C g f p.

Arguments compose {C} _ _ _.


Theorem source_compat : forall (C:Category) (f g:Arr C),
    f == g -> source f == source g.
Proof. intros C f g H. apply compat. assumption. Qed.

Theorem target_compat : forall (C:Category) (f g:Arr C),
    f == g -> target f == target g.
Proof. intros C f g H. apply compat. assumption. Qed.

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

(* We could be asking ourselves whether 'arr' is an embedding
   from the class 'Obj C' to the class 'Arr C'. However, we do
   not have an equality notion on objects, other than that
   induced by 'arr' itself: two objects a and b are deemed
   equal, if and only if they are equal when viewed as arrows:
            a ~ b <-> arr a == arr b
   We are not defining this notion of equality explicitly to
   remind ourselves that equality is only defined on arrows.
*)

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

Lemma src_compat : forall (C:Category) (f g:Arr C), 
    f == g -> arr (src f) == arr (src g).
Proof. intros C f g H. apply source_compat. assumption. Qed.

Lemma tgt_compat : forall (C:Category) (f g:Arr C), 
    f == g -> arr (tgt f) == arr (tgt g).
Proof. intros C f g H. apply target_compat. assumption. Qed.

(* homset defined as a type *)
Inductive Hom (C:Category) (a b:Obj C) : Type :=
| hom : forall (f:Arr C), (source f == arr a) -> (target f == arr b) -> Hom C a b
.

Arguments Hom {C} _ _.
Arguments hom {C} {a} {b} _ _ _.

(* can't see a way to prove this *)
Axiom Hom_compat : forall (C:Category) (a a' b b':Obj C),
    arr a == arr a' -> arr b == arr b' -> Hom a b = Hom a' b'.


(* converting an instance of homset to an arrow *)
Definition i (C:Category) (a b:Obj C) (f:Hom a b) : Arr C :=
    match f with
    | hom f _ _ => f
    end. 

Arguments i {C} {a} {b} _.

(* TODO
Definition j (C:Catgeory) (f:Arr C) : Hom (src f) (tgt f) :=
    hom
*)

(* We could be asking ourselves whether 'i' is an embedding
   from the type 'Hom a b' to the class 'Arr C'. However, we 
   do not have an equality notion on elements of Hom a b, other 
   than that induced by 'i' itself: two elements of Hom a b are
   deemed equal, if and only if they are equal when viewed as 
   as elements of arrows:
            f ~ g  <-> i f == i g
   We are not defining this notion of equality explicitly to
   remind ourselves that equality is only defined on arrows.
*)




Lemma source_of_identity : forall (C:Category) (a:Obj C), source (arr a) == arr a.
Proof. intros C [a H]. simpl. assumption. Qed.

Lemma target_of_identity : forall (C:Category) (a:Obj C), target (arr a) == arr a.
Proof. intros C [a H]. simpl.
    assert (target (source a) == source a) as H'. { apply proof_ts_. }
    assert (target a == target (source a)) as H''.  
        { apply compat. apply sym. assumption. }
    apply trans with (target (source a)).
        - assumption.
        - apply trans with (source a).
            + assumption.
            + assumption.
Qed.

Arguments source_of_identity {C} _.
Arguments target_of_identity {C} _.

(* identity arrow associated with an object *)
Definition id (C:Category) (a:Obj C) : Hom a a :=
    hom (arr a) (source_of_identity a) (target_of_identity a).

Arguments id {C} _.

Lemma id_compat : forall (C:Category) (a b:Obj C),
    arr a == arr b ->  i (id a) == i (id b).
Proof. intros C [a Ha] [b Hb] H. assumption. Qed.


(* needed to construct composition of arrows *)
Lemma compose_defined : forall (C:Category) (a b c:Obj C) (g:Hom b c) (f:Hom a b),
    target (i f) == source (i g).
Proof.
    intros C [a Ha] [b Hb] [c Hc] [g Ag Bg] [f Af Bf]. 
    simpl. simpl in Bf. simpl in Ag. apply trans with b.
        - assumption.
        - apply sym. assumption.
Qed.

Arguments compose_defined {C} {a} {b} {c} _ _.

(* composition of arrows *)
Definition compose_arrow (C:Category)(a b c:Obj C)(g:Hom b c)(f:Hom a b): Arr C :=
    compose_ C (i g) (i f) (compose_defined g f). 

Arguments compose_arrow {C} {a} {b} {c} _ _.

(* we want composition of arrows to be typed, so proving its source *)
Lemma compose_source : forall (C:Category)(a b c:Obj C)(g:Hom b c)(f:Hom a b),
    source (compose_arrow g f) == arr a. 
Proof. 
    intros C [a Ha] [b Hb] [c Hc] [g Ag Bg] [f Af Bf].
    simpl. unfold compose_arrow. simpl. unfold source.
    simpl in Af. apply trans with (source f).
    - apply (proof_src_ C f g).
    - assumption.
Qed.

Arguments compose_source {C} {a} {b} {c} _ _.

(* we want composition of arrows to be typed, so proving its target *)
Lemma compose_target : forall (C:Category)(a b c:Obj C)(g:Hom b c)(f:Hom a b),
    target (compose_arrow g f) == arr c. 
Proof. 
    intros C [a Ha] [b Hb] [c Hc] [g Ag Bg] [f Af Bf].
    simpl. unfold compose_arrow. simpl. unfold target.
    simpl in Bg. apply trans with (target g).
    - apply (proof_tgt_ C f g).
    - assumption.
Qed.

Arguments compose_target {C} {a} {b} {c} _ _.

(* we can now defined composition as a typed operation which is total *)
Definition compose' (C:Category) (a b c:Obj C) (g:Hom b c) (f:Hom a b) : Hom a c :=
    hom (compose_arrow g f) (compose_source g f) (compose_target g f). 

Arguments compose' {C} {a} {b} {c} _ _.

(* syntactic sugar *)
Notation "g # f" := (compose' g f) (at level 60, right associativity) : categ. 

Open Scope categ.

Lemma compose_compat:forall(C:Category)(a b c:Obj C)(f f':Hom a b)(g g':Hom b c),
    i f == i f' -> i g == i g' -> i (g # f) == i (g' # f').
Proof.
    intros C [a Ha] [b Hb] [c Hc] [f Af Bf] [f' Af' Bf'] [g Ag Bg] [g' Ag' Bg']. 
    simpl. unfold compose_arrow. apply proof_compat_.
Qed.

(* composition is associative *)
Theorem compose_assoc : forall (C:Category)(a b c d:Obj C),
    forall (f:Hom a b) (g:Hom b c) (h:Hom c d),
        i (h # (g # f)) == i ((h # g) # f).
Proof.
    intros C [a Ha] [b Hb] [c Hc] [d Hd] [f Af Bf] [g Ag Bg] [h Ah Bh].
    unfold compose, compose_arrow. simpl. apply proof_asc_.
Qed.

(* identity to the left *)
Theorem id_left : forall (C:Category) (a b:Obj C) (f: Hom a b),
    i (id b # f) == i f.
Proof.
    intros C [a Ha] [b Hb] [f Af Bf]. unfold compose, compose_arrow. simpl.
    apply proof_idl_. apply sym. assumption.
Qed.

(* identity to the right *)
Theorem id_right : forall (C:Category) (a b:Obj C) (f: Hom a b),
    i (f # id a) == i f.
Proof.
    intros C [a Ha] [b Hb] [f Af Bf]. unfold compose, compose_arrow. simpl.
    apply proof_idr_. apply sym. assumption.
Qed.




