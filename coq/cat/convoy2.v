
Lemma my_trans : forall (A:Type) (x y z:A),
    x = y -> y = z -> x = z.
Proof. intros A x y z Exy Eyz. rewrite Exy, Eyz. reflexivity. Qed.

Check my_trans.
Check eq_trans.

Definition prop1 : Prop := forall (A:Type) (x y z:A),
    x = y -> y = z -> x = z.


Definition prop2 : Prop := forall (B:Type) (x' y' z':B),
    x' = y' -> y' = z' -> x' = z'.

Lemma prop_same : prop1 = prop2.
Proof. reflexivity. Qed.


Lemma trans2 : forall (A:Type) (x y y' z:A),
    y = y' -> x = y -> y' = z -> x = z.
Proof. intros A x y y' z H Exy Eyz. rewrite Exy, H, Eyz. reflexivity. Qed.

Arguments trans2 {A} {x} {y} {y'} {z} _ _ _.

Definition proof1 (A:Type) (x y z:A) (p:x = y) (q:y = z) : x = z :=
  @eq_trans A x y z p q.  

Parameter eq_bool : forall (A:Type), A -> A -> bool.

Arguments eq_bool {A} _ _.

Axiom eq_bool_correct : forall (A:Type) (x y:A),
    eq_bool x y = true <-> x = y.

Lemma eq_bool_x_x : forall (A:Type) (x:A),
    eq_bool x x = true.
Proof. intros A x. apply eq_bool_correct. reflexivity. Qed.


Definition to_proof (A:Type) (x y:A) (p: eq_bool x y = true) : x = y.
Proof. apply eq_bool_correct. exact p. Qed.

Arguments to_proof {A} {x} {y} _.


Definition to_proof2 (A:Type)(x y:A)(b:bool)(p:eq_bool x y = b) : option(x = y) :=
    match b as b1 return eq_bool x y = b1 -> option (x = y) with
    | true      => fun pr   => Some (to_proof pr)
    | false     => fun _    => None 
    end p.

Arguments to_proof2 {A} {x} {y} _ _.

Definition to_proof3 (A:Type) (x y:A) : option (x = y) :=
    to_proof2 (eq_bool x y) (eq_refl (eq_bool x y)). 


Arguments to_proof3 {A} _ _.


Lemma Correctness2 : forall (A:Type) (x:A) (b:bool) (p:eq_bool x x = b),
    to_proof2 b p <> None.
Proof.
    intros A x b p. destruct b eqn:H. 
    - intros H'. inversion H'.
    - exfalso. rewrite (eq_bool_x_x A x) in p. inversion p.
Qed.

Lemma Correctness2' : forall (A:Type) (x y:A) (b:bool) (p:eq_bool x y = b),
    to_proof2 b p <> None -> x = y.
Proof.
    intros A x y b p H. destruct b eqn:H'. 
    - apply eq_bool_correct. exact p.
    - simpl in H. exfalso. apply H. reflexivity.
Qed.


Lemma Correctness1 : forall (A:Type) (x y:A),
    x = y -> to_proof3 x y <> None.
Proof.
    intros A x y H. rewrite H. unfold to_proof3.
    assert (eq_bool y y = true) as H'. { apply eq_bool_x_x. }
    apply Correctness2.
Qed.

Lemma Correctness3 : forall (A:Type) (x y:A),
    x = y <-> to_proof3 x y <> None.
Proof.
    intros A x y. split. 
    - exact (Correctness1 A x y).
    - unfold to_proof3. 
        exact (Correctness2' A x y (eq_bool x y) (eq_refl (eq_bool x y))).
Qed.


(*
Definition proof3 (A:Type) (x y y' z:A)
    (p:x = y)(q:y' = z)(r:eq_bool y y' = true) : x = z := trans2 (to_proof r) p q.

Arguments proof3 {A} {x} {y} {y'} {z} _ _ _.


Definition proof2 (A:Type) (x y y' z:A) (p:x = y) (q:y' = z) : option (x = z) := 
    match eq_bool y y' as b return eq_bool y y' = b -> option (x = z) with
    | true      => fun pr   => Some (proof3 p q pr)
    | false     => fun _    => None
    end (eq_refl (eq_bool y y')). 
 
Arguments proof2 {A} {x} {y} {y'} {z} _ _.


Definition proof4 (A:Type) (x y y' z:A) 
    (p:x = y) (q:y' = z) (b:bool) (r:eq_bool y y' = b) : option (x = z) :=
        match b as b1 return eq_bool y y' = b1 -> option (x = z) with
        | true      => fun pr => Some (proof3 p q pr)
        | false     => fun _  => None
        end r.

Arguments proof4 {A} {x} {y} {y'} {z} _ _ _ _.

Lemma same24 : forall (A:Type) (x y y' z:A) (p:x = y) (q:y' = z),
    proof2 p q = proof4 p q true (eq_refl (eq_bool y y)).

*)


