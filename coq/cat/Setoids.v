Record Setoid : Type := setoid 
    { elems : Type
    ; equal : elems -> elems -> Prop
    ; refl  : forall (x:elems), equal x x
    ; sym   : forall (x y:elems), equal x y -> equal y x
    ; trans : forall (x y z:elems), equal x y -> equal y z -> equal x z
    }
    .

Arguments equal {s} _ _.
Arguments refl {s} {x}.
Arguments sym {s} {x} {y} _.
Arguments trans {s} {x} {y} {z} _ _. 

Notation "x == y" := (equal x y) (at level 90, no associativity).

(* every type induces a setoid with usual leibniz equality *)
Definition toSetoid (a:Type) : Setoid :=
    setoid a eq (@eq_refl a) (@eq_sym a) (@eq_trans a).


(* a map between setoids is a normal function which preserves equality *)
(* We are here defining a new type for maps between setoids.           *)
Record Hom (a b:Setoid) : Type := hom
    { func    : elems a -> elems b
    ; compat  : forall (x y:elems a), x == y -> func x == func y
    }
    .

Arguments hom {a} {b} _ _.
Arguments func {a} {b} _ _.
Arguments compat {a} {b} _ _ _ _.


Definition eq_Hom (a b:Setoid) (f g:Hom a b) : Prop :=
    forall (x:elems a), func f x == func g x.  

Arguments eq_Hom {a} {b} _ _.

Lemma eq_Hom_refl : forall (a b:Setoid) (f:Hom a b), eq_Hom f f.
Proof.
    intros a b [f H]. unfold eq_Hom. simpl. intros x. apply refl.
Qed.

Arguments eq_Hom_refl {a} {b} _ _.

Lemma eq_Hom_sym : forall (a b:Setoid) (f g:Hom a b), eq_Hom f g -> eq_Hom g f.
Proof.
    intros a b [f Hf] [g Hg]. unfold eq_Hom. simpl. 
    intros H. intros x. apply sym. apply H.
Qed.

Arguments eq_Hom_sym {a} {b} _ _ _ _.


Lemma eq_Hom_trans : forall (a b:Setoid) (f g h:Hom a b), 
    eq_Hom f g -> eq_Hom g h -> eq_Hom f h.
Proof.
    intros a b [f Hf] [g Hg] [h Hh]. unfold eq_Hom. simpl.
    intros Efg Egh x. apply @trans with (y:= g x).
    - apply Efg.
    - apply Egh.
Qed.

Arguments eq_Hom_trans {a} {b} _ _ _ _ _ _.

Definition HomSet (a b:Setoid) : Setoid := setoid 
    (Hom a b)(@eq_Hom a b)(@eq_Hom_refl a b)(@eq_Hom_sym a b)(@eq_Hom_trans a b).

Definition id_func (a:Setoid) (x:elems a) : elems a := x.
 
Arguments id_func {a} _.

Lemma id_compat : forall (a:Setoid) (x y:elems a), 
    x == y -> id_func x == id_func y.
Proof. 
    intros [a eq refl sym trans] x y. simpl. unfold id_func. intros H. exact H. 
Qed.

Arguments id_compat {a} _ _ _.

Definition id (a:Setoid) : Hom a a := hom id_func id_compat. 


Definition compose_func (a b c:Setoid)(g:Hom b c)(f:Hom a b)(x:elems a):elems c :=
    func g (func f x).

Arguments compose_func {a} {b} {c} _ _ _.

Lemma compose_compat : forall (a b c:Setoid) (g:Hom b c) (f:Hom a b) (x y:elems a),
    x == y -> compose_func g f x ==  compose_func g f y.
Proof.
    intros a b c [g Hg] [f Hf] x y E. unfold compose_func. simpl.
    apply Hg, Hf. exact E.
Qed.

Arguments compose_compat {a} {b} {c} _ _ _ _ _.

Definition compose (a b c:Setoid)(g:Hom b c)(f:Hom a b):Hom a c := hom
    (compose_func g f) (compose_compat g f).

Arguments compose {a} {b} {c} _ _.

Notation "g @ f" := (compose g f) (at level 60, right associativity).

Notation "f === g" := (eq_Hom f g) (at level 90, no associativity).

Lemma compose_assoc : forall (a b c d:Setoid) (h:Hom c d) (g:Hom b c) (f:Hom a b),
    (h @ g) @ f === (h @ g) @ f.
Proof.
    intros a b c d [h Hh] [g Hg] [f Hf]. unfold compose, eq_Hom. simpl. intros x.
    apply Hh, Hg, Hf. apply refl.  
Qed.


Lemma id_left : forall (a b:Setoid) (f:Hom a b), (id b) @ f === f.
Proof.
    intros a b [f Hf]. unfold compose, id, eq_Hom, id_func. simpl. intros x.
    apply Hf. apply refl.  
Qed.

Lemma id_right : forall (a b:Setoid) (f:Hom a b), f @ (id a) === f.
Proof.
    intros a b [f Hf]. unfold compose, id, eq_Hom, id_func. simpl. intros x.
    apply Hf. apply refl.  
Qed.
