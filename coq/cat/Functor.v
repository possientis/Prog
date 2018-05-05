Require Import Setoids.
Require Import Category7.

Record Functor (C D:Category) : Type := functor
    { Func_         : Arr C -> Arr D
    ; Func_compat_  : forall (f g:Arr C), f == g -> Func_ f == Func_ g
    ; Func_source_  : forall (f:Arr C), source (Func_ f) == Func_ (source f)
    ; Func_target_  : forall (f:Arr C), target (Func_ f) == Func_ (target f)
    ; Func_compose_ : forall (f g:Arr C),
        forall (p: target f == source g) (q: target (Func_ f) == source (Func_ g)),
        Func_ (compose_ C g f p) == compose_ D (Func_ g) (Func_ f) q
      
    }
    .

Arguments Func_ {C} {D} _ _.

Lemma Functor_obj_ : forall (C D:Category)(F:Functor C D)(a:Arr C),
    source a == a -> source (Func_ F a) == Func_ F a.
Proof.
    intros C D F a H. apply trans with (Func_ F (source a)).
    - apply Func_source_.
    - apply Func_compat_. assumption.
Qed.

Arguments Functor_obj_ {C} {D} _ _ _.


Definition apply (C D:Category) (F:Functor C D)(a:Obj C) : Obj D :=
    match a with 
    | obj a' p      => obj (Func_ F a') (Functor_obj_ F a' p)
    end.

Arguments apply {C} {D} _ _.

Notation "F $ a" := (apply F a) (at level 0, right associativity) : categ.

Definition lift_arrow_(C D:Category)(a b:Obj C)(F:Functor C D)(f:Hom a b):Arr D :=
    match f with
    | hom f' p q    => Func_ F f'
    end.

Arguments lift_arrow_ {C} {D} {a} {b} _ _.

Definition lift_source_:forall (C D:Category)(a b:Obj C)(F:Functor C D)(f:Hom a b),
    source (lift_arrow_ F f) == arr (F $ a).
Proof.
    intros C D [a Ha] [b Hb] F [f p q]. simpl. simpl in p.
    apply trans with (Func_ F (source f)).
    - apply Func_source_.
    - apply Func_compat_. assumption.
Qed.

Arguments lift_source_ {C} {D} {a} {b} _ _.
     
Open Scope categ.

Definition lift_target_:forall (C D:Category)(a b:Obj C)(F:Functor C D)(f:Hom a b),
    target (lift_arrow_ F f) == arr F $ b.
Proof.
    intros C D [a Ha] [b Hb] F [f p q]. simpl. simpl in q.
    apply trans with (Func_ F (target f)).
    - apply Func_target_.
    - apply Func_compat_. assumption.
Qed.

Arguments lift_target_ {C} {D} {a} {b} _ _.

Definition lift(C D:Category)(a b:Obj C)(F:Functor C D)(f:Hom a b):
  Hom (F $ a) (F $ b) := hom (lift_arrow_ F f)(lift_source_ F f)(lift_target_ F f).

Arguments lift {C} {D} {a} {b} _ _.

Notation "F <$> f" := (lift F f) (at level 0, right associativity) : categ.


Lemma functor_id : forall (C D:Category) (F:Functor C D) (a:Obj C),
    i F<$>(id a) == i (id F $ a).
Proof. intros C D F [a Ha]. simpl. apply refl. Qed.

Lemma functor_law : forall (C D:Category) (F:Functor C D) (a b c:Obj C),
    forall (g:Hom b c) (f:Hom a b), i F<$>(g # f) == i (F<$>g # F<$>f).
Proof.
    intros C D F [a Ha] [b Hb] [c Hc] [g Ag Bg] [f Af Bf]. simpl.
    unfold compose_arrow. simpl. apply Func_compose_.
Qed.










