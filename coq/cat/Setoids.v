Require Import Eq.
Require Category6.

Module Cat := Category6.

Record Setoid : Type := setoid 
    { elems     : Type
    ; eqElems   : Eq elems
    }
    .

Arguments eqElems {s}.

Notation "x === y" := (equal eqElems x y) (at level 90, no associativity).

Lemma set_relf  : forall (a:Setoid) (x:elems a), 
    x === x.
Proof. intros a x. apply refl. Qed.

Lemma set_sym   : forall (a:Setoid) (x y:elems a), 
    x === y -> y === x.
Proof. intros a x y. apply sym. Qed.

Lemma set_trans : forall (a:Setoid) (x y z:elems a), 
    x === y -> y === z -> x === z.
Proof. intros a x y z. apply trans. Qed.

(* every type induces a setoid with usual leibniz equality *)
Definition toSetoid (a:Type) : Setoid := setoid a defEq.

(* a map between setoids is a normal function which preserves equality *)
(* We are here defining a new type for maps between setoids.           *)
Record Hom_ (a b:Setoid) : Type := hom
    { func    : elems a -> elems b
    ; compat  : forall (x y:elems a), x === y -> func x === func y
    }
    .
Arguments hom {a} {b} _ _.
Arguments func {a} {b} _ _.
Arguments compat {a} {b} _ _ _ _.


Definition eq_Hom (a b:Setoid) (f g:Hom_ a b) : Prop :=
    forall (x:elems a), func f x === func g x.  

Arguments eq_Hom {a} {b} _ _.

Lemma eq_Hom_refl : forall (a b:Setoid) (f:Hom_ a b), eq_Hom f f.
Proof.
    intros a b [f H]. unfold eq_Hom. simpl. intros x. apply refl.
Qed.

Arguments eq_Hom_refl {a} {b} _ _.

Lemma eq_Hom_sym : forall (a b:Setoid) (f g:Hom_ a b), eq_Hom f g -> eq_Hom g f.
Proof.
    intros a b [f Hf] [g Hg]. unfold eq_Hom. simpl. 
    intros H. intros x. apply sym. apply H.
Qed.

Arguments eq_Hom_sym {a} {b} _ _ _ _.


Lemma eq_Hom_trans : forall (a b:Setoid) (f g h:Hom_ a b), 
    eq_Hom f g -> eq_Hom g h -> eq_Hom f h.
Proof.
    intros a b [f Hf] [g Hg] [h Hh]. unfold eq_Hom. simpl.
    intros Efg Egh x. apply @trans with (y:= g x).
    - apply Efg.
    - apply Egh.
Qed.

Arguments eq_Hom_trans {a} {b} _ _ _ _ _ _.

Definition eqHomSetoid (a b:Setoid) : Eq (Hom_ a b) := equality
    eq_Hom eq_Hom_refl eq_Hom_sym eq_Hom_trans.

Definition Hom (a b:Setoid) : Setoid := setoid 
    (Hom_ a b) (eqHomSetoid a b).

Notation "a ==> b" := (Hom a b) (at level 60, right associativity).

Definition prod_ (a b:Setoid) : Type := (elems a * elems b).

Definition prod_eq (a b:Setoid) : Eq (prod_ a b) := prodEq eqElems eqElems. 

Definition prod (a b:Setoid) : Setoid := setoid (prod_ a b) (prod_eq a b).


Definition apply_ (a b:Setoid) : elems (prod (a ==> b) a) -> elems b :=
    fun arg => match arg with
               | (f,x)  => func f x
               end.

Arguments apply_ {a} {b} _.

Lemma apply_compat : forall (a b:Setoid) (y y':elems (prod (a ==> b) a)),
    y === y' -> apply_ y === apply_ y'.
Proof.
    intros a b [f x] [f' x'] [H1 H2]. 
    simpl. simpl in H1. simpl in H2.
    assert (func f x === func f x') as H.
    { apply compat. exact H2. }
    apply set_trans with (y:= func f x').
        - exact H.
        - apply H1.
Qed.

Arguments apply_compat {a} {b}.

Definition apply (a b:Setoid) : elems ((prod (a ==> b) a) ==> b) := 
    hom apply_ apply_compat.
    

Definition id_func (a:Setoid) (x:elems a) : elems a := x.
 
Arguments id_func {a} _.

Lemma id_compat : forall (a:Setoid) (x y:elems a), 
    x === y -> id_func x === id_func y.
Proof. 
    intros a x y. simpl. unfold id_func. intros H. exact H. 
Qed.

Arguments id_compat {a} _ _ _.

Definition id (a:Setoid) : elems (Hom a a) := hom id_func id_compat. 

(*
Definition compose_func (a b c:Setoid)(g:Hom b c)(f:Hom a b)(x:elems a):elems c :=
    func g (func f x).

Arguments compose_func {a} {b} {c} _ _ _.
*)
(*
Lemma compose_compat : forall (a b c:Setoid) (g:Hom b c) (f:Hom a b) (x y:elems a),
    x === y -> compose_func g f x ===  compose_func g f y.
Proof.
    intros a b c [g Hg] [f Hf] x y E. unfold compose_func. simpl.
    apply Hg, Hf. exact E.
Qed.

Arguments compose_compat {a} {b} {c} _ _ _ _ _.

Definition compose (a b c:Setoid)(g:Hom b c)(f:Hom a b):Hom a c := hom
    (compose_func g f) (compose_compat g f).

Arguments compose {a} {b} {c} _ _.

Notation "g # f" := (compose g f) (at level 60, right associativity).

Notation "f =~ g" := (embed f === embed g) (at level 90, no associativity).

Lemma compose_assoc : forall (a b c d:Setoid)(f:Hom a b)(g:Hom b c)(h:Hom c d),
    (h # g) # f =~ (h # g) # f.
Proof.
    intros a b c d [f Hf] [g Hg] [h Hh]. unfold compose, eq_Hom. simpl. intros x.
    apply Hh, Hg, Hf. apply refl.  
Qed.

Lemma id_left : forall (a b:Setoid) (f:Hom a b), (id b) # f =~ f.
Proof.
    intros a b [f Hf]. unfold compose, id, eq_Hom, id_func. simpl. intros x.
    apply Hf. apply refl.  
Qed.

Lemma id_right : forall (a b:Setoid) (f:Hom a b), f # (id a) =~ f.
Proof.
    intros a b [f Hf]. unfold compose, id, eq_Hom, id_func. simpl. intros x.
    apply Hf. apply refl.  
Qed.

Definition compatible (a:Setoid) (P:elems a -> Prop) : Prop :=
    forall (x y:elems a), x === y -> P x -> P y.

Arguments compatible {a} _.

Lemma rewriteSetoid : forall (a:Setoid) (P:elems a -> Prop),
    forall (x y:elems a), compatible P -> x === y -> P x -> P y.
Proof. intros a P x y H. apply H. Qed.

Lemma composition_is_compat : forall (a b c:Setoid)(f f':Hom a b)(g g':Hom b c),
    f =~ f' -> g =~ g' -> g # f =~ g' # f'.
Proof.
    intros a b c f f' g g' Ef Eg. 
    unfold embed. simpl. unfold eq_Hom. intros x. 
    simpl in Eg. unfold eq_Hom in Eg. unfold embed in Eg.
    simpl in Ef. unfold eq_Hom in Ef. unfold embed in Ef.
    unfold compose. simpl. unfold compose_func. 
    assert (func f x === func f' x) as E. { apply Ef. }
    assert (func g (func f x) === func g (func f' x)) as H.
        { apply (compat g). exact E. }
    apply set_trans with (y:=func g (func f' x)).
    -  exact H.
    -  apply Eg.
Qed.


Definition setoidsAsCategory : Cat.Category := Cat.category 
    Setoid 
    Hom 
    (@compose) 
    id 
    eqHomSetoid 
    id_left 
    id_right
    compose_assoc
    composition_is_compat.
*)










    


