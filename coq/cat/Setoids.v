Record Setoid : Type := setoid 
    { elems : Type
    ; equal : elems -> elems -> Prop
    ; refl  : forall (x:elems), equal x x
    ; sym   : forall (x y:elems), equal x y -> equal y x
    ; trans : forall (x y z:elems), equal x y -> equal y z -> equal x z
    }
    .

(* every type induces a setoid with usual leibniz equality *)
Definition toSetoid (a:Type) : Setoid :=
    setoid a eq (@eq_refl a) (@eq_sym a) (@eq_trans a).

(* a map between setoids is a normal function which preserves equality *)
Record Map (a b:Setoid) : Type := hom
    { apply : elems a -> elems b
    ; comp  : forall (x y:elems a), equal a x y -> equal b (apply x) (apply y)
    }
    .

Arguments apply {a} {b} _.


Definition eq_Map (a b:Setoid) (f g:Map a b) : Prop :=
    forall (x:elems a), equal b (apply f x) (apply g x).  

Arguments eq_Map {a} {b} _ _.


Lemma eq_Map_refl : forall (a b:Setoid) (f:Map a b), eq_Map f f.
Proof.
    intros a b [f H]. unfold eq_Map. simpl. intros x. apply (refl b).
Qed.

Arguments eq_Map_refl {a} {b} _.

Lemma eq_Map_sym : forall (a b:Setoid) (f g:Map a b), eq_Map f g -> eq_Map g f.
Proof.
    intros a b [f Hf] [g Hg]. unfold eq_Map. simpl. 
    intros H. intros x. apply (sym b). apply H.
Qed.

Arguments eq_Map_sym {a} {b} _ _ _.


Lemma eq_Map_trans : forall (a b:Setoid) (f g h:Map a b), 
    eq_Map f g -> eq_Map g h -> eq_Map f h.
Proof.
    intros a b [f Hf] [g Hg] [h Hh]. unfold eq_Map. simpl.
    intros Efg Egh x. apply (trans b) with (y:= g x).
    - apply Efg.
    - apply Egh.
Qed.

Arguments eq_Map_trans {a} {b} _ _ _ _ _.


Definition Hom (a b:Setoid) : Setoid := setoid 
    (Map a b)(@eq_Map a b)(@eq_Map_refl a b)(@eq_Map_sym a b)(@eq_Map_trans a b).


