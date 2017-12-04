(* In general, given (A:Type) and (x y:A) it is not possible 
   write code which tests whether x = y or not. *)

(* However, let us assume we are given a type *)
Parameter A:Type.

(* for which a decision function exists *)
Parameter eq_bool : A -> A -> bool.

(* Of course we assume this decision function has the correct semantics *)
Axiom eq_bool_correct : forall (x y:A),
    eq_bool x y = true <-> x = y.

(* In particular we have the following *)
Lemma eq_bool_x_x : forall (x:A), eq_bool x x = true.
Proof. intros x. apply eq_bool_correct. reflexivity. Qed. 

(* Also, we can define a function, which given a proof of 
   'eq_bool x y = true', returns a proof of 'x = y'   *)

Definition to_proof (x y:A) (p:eq_bool x y = true) : x = y.
Proof. apply eq_bool_correct. exact p. Qed.


(* Ok, so at this stage, we have (A:Type) which is no longer
   an arbitrary type, but is instead a type for which we have 
   some tools at our disposal. Can we now write code which tests
   whether x = y or not ? *)


(* we would like to write a function 'test' which returns 'Some' 
   proof of x = y whenever the arguments are equal, or 'None' *)

(* The immediate attempt is *)

(* This code fails
Definition test1 (x y:A) : option (x = y) :=
    match eq_bool x y with
    | true      =>  Some (to_proof x y _)
    | false     =>  None 
    end.
*)

(* However, this cannot work because within the branch of the pattern
   match corresponding to eq_bool x y = true, we do not have a proof
   of this fact at our disposal, to feed into the 'to_proof' function *)

(* So let us try something else *)
Definition test2 (x y:A) : option (x = y) :=
    match eq_bool x y as b return eq_bool x y = b -> option (x = y) with
    | true      => fun p    => Some (to_proof x y p)
    | fasle     => fun _    => None
    end (eq_refl (eq_bool x y)). 


(* This code compiles successfully and looks like it is doing the right thing *)

(* However, for our function 'test2' to be useful, we need to be able to prove
   that is has the correct semantics *)

Lemma test2_correct_fail : forall (x y: A),
    x = y <-> test2 x y <> None.
Proof.
    intros x y. split.
    - intros Exy. rewrite Exy. unfold test2. 
    (* rewrite (eq_bool_x_x y). *)
    Abort.

(* when attempting to prove the implication x = y -> test2 x y <> None, it 
   is natural to rewrite the assumption x = y to obtain a goal test2 y y <> None.
   After unfolding test2, we see a goal involving a condition on eq_bool y y.
   At this stage we would like to use the fact that eq_bool y y = true, that is
   we would like to rewrite (eq_bool_x_x y). However this create a typing
   error, seemingly because 'eq_bool y y' appears in several places within the
   match expression, and replacing all of these occurrences by 'true' creates
   a term which is ill-typed *)


(* A solution to this problem is to abstract away the boolean value which
   represents eq_bool x y as well as the proof of the fact that eq_bool x y = b *)

(* So let us define a new function *)
Definition test3 (x y:A) (b:bool) (p:eq_bool x y = b) : option (x = y) :=
    match b as b1 return eq_bool x y = b1 -> option (x = y) with
    | true      => fun q    => Some (to_proof x y q)
    | false     => fun _    => None
    end p.

(* The hope is the proving correctness properties with test3 will be easier *)

(* Of course, the function test3 still has a relation to our initial test2 *)

Lemma test2_test3 : forall (x y:A),
    test2 x y = test3 x y (eq_bool x y) (eq_refl (eq_bool x y)).
Proof. reflexivity. Qed.

(* Let us attempt to prove some correctness properties on test3 *)

Lemma test3_correct1 : forall (x:A) (b:bool) (p:eq_bool x x = b),
    test3 x x b p <> None.
Proof. 
    intros x b p H. destruct b eqn:H'.
    - inversion H.
    - clear H. rewrite eq_bool_x_x in p. inversion p. 
Qed.
        


Lemma test3_correct2 : forall (x y:A) (b:bool) (p:eq_bool x y = b),
    test3 x y b p <> None -> x = y.
Proof.
    intros x y b p H. destruct b eqn:H'.
    - apply eq_bool_correct. exact p.
    - unfold test3 in H. exfalso. apply H. reflexivity.
Qed.

(* Now that we have correctness results in terms of test3, the hope is
   to achieve correctness result for test2  *)

Lemma test2_correct : forall (x y:A),
    x = y <-> test2 x y <> None.
Proof.
    intros x y. split.
    - intros H. rewrite H. apply test3_correct1.
    - intros H. 
        apply (test3_correct2 x y (eq_bool x y) (eq_refl (eq_bool x y))).
        exact H.
Qed.

(* This was quite painful, but here we have it: we have a primitive test2
   which returns Some proof of x = y whenever x and y are equal and None
   otherwise, and crucially we have a correctness result which will allow
   us to prove things about our code. So we can now write code which tests 
   whether x and y are equal by pattern matching on test2 x y (which gives
   a proof of x = y on the corresponding branch). This is a lot better 
   than pattern matching on eq_bool x y which does not give us evidence
   within the code of the fact that x = y, or if it does (using the convoy
   pattern), it is highly inflexible as basic rewrites lead to ill-typed 
   terms. *)


(* Application *)

Lemma trans2 : forall (x y y' z:A), y = y' -> x = y -> y' = z -> x = z.
Proof. intros x y y' z H. rewrite H. apply eq_trans. Qed.


Definition get_proof (x y y' z:A) (pxy : x = y) (pyz: y' = z) : option (x = z) :=
    match test2 y y' with
    | Some pyy      => Some (trans2 x y y' z pyy pxy pyz)
    | None          => None
    end.

Lemma get_proof_correct : forall (x y y' z:A) (pxy : x = y) (pyz: y' = z),
    y = y' <-> get_proof x y y' z pxy pyz <> None.
Proof.
    intros x y y' z pxy pyz. split.
    - intros H. destruct (test2 y y') eqn:H'.
        + unfold get_proof. rewrite H'. intros H0. inversion H0.
        + apply test2_correct in H. exfalso. apply H. exact H'.
    - intros H. destruct (test2 y y') eqn:H'.
        + apply test2_correct. intros H0. rewrite H0 in H'. inversion H'.
        + unfold get_proof in H. rewrite H' in H. exfalso. apply H. reflexivity.
Qed.


(* In effect, we have proved the existence of a 'proof function'
   which has the correct semantics *)

Theorem proof_func_exists : exists (f: forall (x y:A), option (x = y)),
    forall (x y:A), x = y <-> f x y <> None.
Proof. exists test2. exact test2_correct. Qed.


(* This was obtained from the existence of a correct boolean decision function *)

(* Let us try and go the other way, from a correct proof function,
   to a correct boolean decision function *)

Parameter test: forall (x y:A), option (x = y).

Axiom test_correct : forall (x y:A), x = y <-> test x y <> None.


Definition eq_bool2 (x y:A) : bool :=
    match test x y with
    | Some _        => true
    | None          => false
    end.

Lemma eq_bool2_correct : forall (x y:A), 
    eq_bool2 x y = true <-> x = y.
Proof.
    intros x y. split.
    - intros H. destruct (test x y) eqn:H'. 
        + apply test_correct. intros H0. rewrite H0 in H'. inversion H'.
        + unfold eq_bool2 in H. rewrite H' in H. inversion H.
    - intros H. destruct (test x y) eqn:H'.
        + unfold eq_bool2. rewrite H'. reflexivity.
        + apply test_correct in H. exfalso. apply H. exact H'.
Qed.


Definition has_boolean_func (a:Type) : Prop := 
    exists (f: a -> a -> bool), 
        forall (x y:a), x = y <-> f x y = true. 

Definition has_proof_func (a:Type) : Prop := 
    exists (f: forall (x y:a), option (x = y)),
        forall (x y:a), x = y <-> f x y <> None.

Theorem boolean_proof_iff : forall (a:Type),
    has_boolean_func a <-> has_proof_func a.
Proof.

Show.



