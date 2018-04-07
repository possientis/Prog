Require Import Eq.
Require Category6.

Module Cat := Category6.

Record Setoid : Type := setoid 
    { elems     : Type
    ; eqElems   : Eq elems
    }
    .

Arguments eqElems {s}.

Notation "x == y" := (equal eqElems x y) (at level 90, no associativity) : setoid.

Open Scope setoid.

(* every type induces a setoid with usual leibniz equality *)
Definition toSetoid (a:Type) : Setoid := setoid a defEq.

(* a map between setoids is a normal function which preserves equality *)
(* We are here defining a new type for maps between setoids.           *)
Record Hom_ (a b:Setoid) : Type := hom
    { apply   : elems a -> elems b
    ; compat  : forall (x y:elems a), x == y -> apply x == apply y
    }
    .
Arguments hom {a} {b} _ _.
Arguments apply {a} {b} _ _.
Arguments compat {a} {b} _ _ _ _.

Definition HomEq_ (a b:Setoid) (f g:Hom_ a b) : Prop :=
    forall (x:elems a), apply f x == apply g x.  

Arguments HomEq_ {a} {b} _ _.

Lemma HomEq_refl : forall (a b:Setoid) (f:Hom_ a b), HomEq_ f f.
Proof.
    intros a b [f H]. unfold HomEq_. simpl. intros x. apply refl.
Qed.

Arguments HomEq_refl {a} {b} _ _.

Lemma HomEq_sym : forall (a b:Setoid) (f g:Hom_ a b), HomEq_ f g -> HomEq_ g f.
Proof.
    intros a b [f Hf] [g Hg]. unfold HomEq_. simpl. 
    intros H. intros x. apply sym. apply H.
Qed.

Arguments HomEq_sym {a} {b} _ _ _ _.


Lemma HomEq_trans : forall (a b:Setoid) (f g h:Hom_ a b), 
    HomEq_ f g -> HomEq_ g h -> HomEq_ f h.
Proof.
    intros a b [f Hf] [g Hg] [h Hh]. unfold HomEq_. simpl.
    intros Efg Egh x. apply @trans with (y:= g x).
    - apply Efg.
    - apply Egh.
Qed.

Arguments HomEq_trans {a} {b} _ _ _ _ _ _.

Definition HomEq (a b:Setoid) : Eq (Hom_ a b) := equality
    HomEq_ HomEq_refl HomEq_sym HomEq_trans.

Definition Hom (a b:Setoid) : Setoid := setoid 
    (Hom_ a b) (HomEq a b).

Notation "a ~> b" := (elems (Hom a b))(at level 60, right associativity) : setoid.

Definition id_ (a:Setoid) (x:elems a) : elems a := x.
 
Arguments id_ {a} _.

Lemma id_compat : forall (a:Setoid) (x y:elems a), 
    x == y -> id_ x == id_ y.
Proof. 
    intros a x y. simpl. unfold id_. intros H. exact H. 
Qed.

Arguments id_compat {a} _ _ _.

Definition id (a:Setoid) : a ~> a := hom id_ id_compat. 

Definition compose_ (a b c:Setoid)(g:b ~> c)(f:a ~> b)(x:elems a):elems c :=
    apply g (apply f x).

Arguments compose_ {a} {b} {c} _ _ _.

Lemma compose_compat : forall (a b c:Setoid) (g:b ~> c) (f:a ~> b) (x y:elems a),
    x == y -> compose_ g f x ==  compose_ g f y.
Proof.
    intros a b c [g Hg] [f Hf] x y E. unfold compose_. simpl.
    apply Hg, Hf. exact E.
Qed.

Arguments compose_compat {a} {b} {c} _ _ _ _ _.

Definition compose (a b c:Setoid)(g:b ~> c)(f:a ~> b):a ~> c := hom
    (compose_ g f) (compose_compat g f).

Arguments compose {a} {b} {c} _ _.


Notation "g # f" := (compose g f) (at level 60, right associativity).


Lemma compose_assoc : forall (a b c d:Setoid)(f:a ~> b)(g:b ~> c)(h:c ~> d),
    (h # g) # f == (h # g) # f.
Proof.
    intros a b c d [f Hf] [g Hg] [h Hh]. unfold compose, HomEq. simpl. intros x.
    apply Hh, Hg, Hf. apply refl.  
Qed.


Lemma id_left : forall (a b:Setoid) (f:a ~> b), (id b) # f == f.
Proof.
    intros a b [f Hf]. unfold compose, id, HomEq, id_. simpl. intros x.
    apply Hf. apply refl.  
Qed.


Lemma id_right : forall (a b:Setoid) (f:a ~> b), f # (id a) == f.
Proof.
    intros a b [f Hf]. unfold compose, id, HomEq, id_. simpl. intros x.
    apply Hf. apply refl.  
Qed.


Lemma composition_is_compat : forall (a b c:Setoid)(f f':a ~> b)(g g':b ~> c),
    f == f' -> g == g' -> g # f == g' # f'.
Proof.
    intros a b c f f' g g' Ef Eg. 
    simpl. unfold HomEq. intros x. 
    simpl in Eg. unfold HomEq in Eg.
    simpl in Ef. unfold HomEq in Ef.
    unfold compose. simpl. unfold compose_. 
    assert (apply f x == apply f' x) as E. { apply Ef. }
    assert (apply g (apply f x) == apply g (apply f' x)) as H.
        { apply (compat g). exact E. }
    apply trans with (y:=apply g (apply f' x)).
    -  exact H.
    -  apply Eg.
Qed.

Definition setoidsAsCategory : Cat.Category := Cat.category 
    Setoid 
    (fun x y => x ~> y)
    (@compose) 
    id 
    HomEq
    id_left 
    id_right
    compose_assoc
    composition_is_compat.

