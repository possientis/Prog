Require Import Setoid.

Parameter eq_bool : forall (A:Type), A -> A -> bool.

Arguments eq_bool {A} _ _.

Axiom eq_bool_correct : forall (A:Type) (x y:A),
    eq_bool x y = true <-> x = y.

Definition to_proof (A:Type) (x y:A) (p: eq_bool x y = true) : x = y.
Proof. apply eq_bool_correct. exact p. Qed.

Arguments to_proof {A} {x} {y} _.

Lemma eq_bool_false : forall (A:Type) (x y:A),
    eq_bool x y = false -> x <> y.
Proof.
    intros A x y H Exy. rewrite <- eq_bool_correct in Exy.
    rewrite Exy in H. inversion H.
Qed.


(* using eq_refl in definition is going to make it hard to prove 
   anything, as destructing on eq_bool x y is going to create 
   ill-typed terms.                                             *)
Definition test (A:Type) (x y:A) : option (x = y) :=
    match eq_bool x y as b return eq_bool x y = b -> option (x = y) with
    | true  => fun p => Some (to_proof p)
    | false => fun _ => None
    end (eq_refl (eq_bool x y)).

(* We re abstracting over eq_bool x y and over eq_refl *)
Definition test' (A:Type)(x y:A)(b:bool)(p: eq_bool x y = b):option (x = y) := 
    match b as b1 return eq_bool x y = b1 -> option (x = y) with
    | true  => fun p => Some (to_proof p)
    | false => fun _ => None
    end p.

(* Our initial definition is a particular case of the abstracted one *)
Lemma test_test' : forall (A:Type) (x y:A),
    test A x y = test' A x y (eq_bool x y) (eq_refl (eq_bool x y)).
Proof. reflexivity. Qed.


(* Easier to prove things about abstracted definition *)
Theorem basic' : forall (A:Type) (x:A) (b:bool) (p:eq_bool x x = b),
    test' A x x b p <> None.
Proof.
    intros A x b p. destruct b eqn:H.
    - unfold test'. intros H'. inversion H'.
    - unfold test'. exfalso. apply eq_bool_false in p. apply p. reflexivity.
Qed.

(* This allows to get result on initial definition *)
Theorem basic : forall (A:Type) (x y:A),
    x = y -> test A x y <> None.
Proof.
    intros A x y H. rewrite test_test'. rewrite H. apply basic'.
Qed.



