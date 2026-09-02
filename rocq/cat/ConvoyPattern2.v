Inductive A : Type := A1 | A2 | A3.

Inductive Sum (x:A) : Type :=
| pA1 : x = A1 -> Sum x
| pA2 : x = A2 -> Sum x
| pA3 : x = A3 -> Sum x
.

Arguments pA1 {x} _.
Arguments pA2 {x} _.
Arguments pA3 {x} _.

Definition toProof (x:A) : Sum x :=
    match x as y return x = y -> Sum x with
    | A1    => fun p  => pA1 p
    | A2    => fun p  => pA2 p
    | A3    => fun p  => pA3 p
    end (eq_refl x).


Definition toProof_bool(b:bool) : {b = true} + {b = false} :=
    match b as c return b = c -> {b = true} + {b = false} with
    | true  => fun p  => left p
    | false => fun p  => right p
    end (eq_refl b). 

Definition test (b:bool) : {b = true} + {b = false} :=
    match b with
    | true  => left  (eq_refl true)
    | false => right (eq_refl false)
    end.

Lemma equal : forall (b:bool), test b = toProof_bool b.
Proof.
    intros b. destruct b eqn:H.
    - reflexivity.
    - reflexivity.
Qed.

Definition test2 (x:A) : Sum x :=
    match x with
    | A1    => pA1 (eq_refl A1)
    | A2    => pA2 (eq_refl A2)
    | A3    => pA3 (eq_refl A3)
    end.

Lemma equal2 : forall (x:A), test2 x = toProof x.
Proof.
    intros x. destruct x eqn:H.
    - reflexivity.
    - reflexivity.
    - reflexivity.
Qed.




(*
Lemma option_some_not_none : forall (a:Type) (x:option a) (y:a),
    x = Some y -> x <> None.
Proof. intros a x y H H'. rewrite H' in H. inversion H. Qed.

Definition toProof_option (a:Type) (o:option a) : {o <> None} + {o = None} :=
    match o as o' return o = o' -> {o <> None} + {o = None} with
    | Some y    => fun p => left (option_some_not_none a o y p)
    | None      => fun p => right p
    end (eq_refl o).

Arguments toProof_option {a} _.

Parameter B:Type.
Parameter eq_bool : B -> B -> bool.
Axiom eq_bool_true : forall (x y:B), eq_bool x y = true  -> x = y.
Axiom eq_bool_false: forall (x y:B), eq_bool x y = false -> x <> y.


Definition f : forall (x y:B), {x = y} + {x <> y} :=
    fun (x y:B) =>
        match (toProof_bool  (eq_bool x y)) with
        | left p    => left  (eq_bool_true  x y p)
        | right p   => right (eq_bool_false x y p)
        end.

Definition g : forall (x y:B), option (x = y) :=
    fun (x y:B) =>
        match f x y with
        | left p    => Some p
        | right _   => None
        end.

Lemma g_Some : forall (x y:B), g x y <> None -> x = y.
Proof.
    intros x y H. unfold g in H. destruct (f x y) as [e|ne]. 
    - exact e.
    - exfalso. apply H. reflexivity. 
Qed.

Lemma g_None : forall (x y:B), g x y = None -> x <> y.
Proof.
    intros x y H H'. unfold g in H. destruct (f x y) as [e|ne].
    - inversion H.
    - apply ne. exact H'.
Qed.

Definition h : forall (x y:B), {x = y} + {x <> y} :=
    fun (x y:B) =>
        match (toProof_option (g x y)) with
        | left p    =>  left (g_Some x y p)
        | right p   =>  right (g_None x y p)
        end. 
*)







