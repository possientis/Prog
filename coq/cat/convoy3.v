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

Lemma test2_correct : forall (x y: A),
    x = y <-> test2 x y <> None.
Proof.

Show.



