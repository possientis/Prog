Extraction Language Haskell.

Require Import Tactics.   (* Program Definition ... *)

(*
Print Nat.pred.

Extraction Nat.pred.
*)

Lemma zltz : 0 < 0 -> False.
Proof. intros H. inversion H. Qed.

Definition pred_strong1 (n:nat) : (0 < n) -> nat :=
    match n with
    | 0     => (fun p => match zltz p with end)
    | S n   => (fun _           => n)
    end.

Arguments pred_strong1 {n} _.

Lemma zero_lt_one : 0 < 1.
Proof. constructor. Qed.


Lemma pred_strong1_test1 : pred_strong1 zero_lt_one = 0.
Proof. reflexivity. Qed.


Lemma zero_lt_two : 0 < 2.
Proof. auto. Qed.

Lemma pred_strong1_test2 : pred_strong1 zero_lt_two = 1.
Proof. reflexivity. Qed.

(* The term "p" has type "0 < n" while it is expected to have type "0 < 0". *)
Fail Definition pred_strong2 (n:nat) (p:0 < n) : nat :=
    match n with
    | 0     => match zltz p with end
    | S n   => n
    end.
(*
In this case, we must use a return annotation to declare the relationship 
between the value of the match discriminee and the type of the result. 
There is no annotation that lets us declare a relationship between the 
discriminee and the type of a variable that is already in scope; hence, 
****we delay the binding of p****, so that we can use the return annotation 
to express the needed relationship.
*)


Definition pred_strong3 (n:nat) : (0 < n) -> nat :=
    match n return (0 < n) -> nat with 
    | 0     => (fun p => match zltz p with end)
    | S n   => (fun _ => n)
    end.

Definition pred_strong4 (n:nat) (p: 0 < n) : nat :=
    let f := match n return (0 < n) -> nat with 
        | 0     => (fun q => match zltz q with end)
        | S n   => (fun _ => n)
        end
    in f p.

(*
Extraction pred_strong1.

pred_strong1 :: Nat -> Nat
pred_strong1 n = case n of 
    O   -> error "absurd case"
    S n -> n
*)

(*
Print sig.

Inductive sig (A : Type) (P : A -> Prop) : Type :=
    exist : forall x : A, P x -> {x : A | P x}

    For sig: Argument A is implicit
    For exist: Argument A is implicit
    For sig: Argument scopes are [type_scope type_scope]
    For exist: Argument scopes are [type_scope function_scope _ _]
*)

(*
Print ex.
Inductive ex (A : Type) (P : A -> Prop) : Prop :=
    ex_intro : forall x : A, P x -> exists y, P y

    For ex: Argument A is implicit
    For ex_intro: Argument A is implicit
    For ex: Argument scopes are [type_scope function_scope]
    For ex_intro: Argument scopes are [type_scope function_scope _ _]
*)

(*
Locate "{ _ : _ | _ }".
Notation            Scope     
"{ x : A  |  P }" := sig (fun x => P) : type_scope (default interpretation
*)


Definition pred_strong5 (n : {x : nat | 0 < x}) : nat :=
    match n with
    | exist _ 0     p => match zltz p with end
    | exist _ (S n) _ => n
    end.

Definition n1 : {x : nat | 0 < x} := exist _ 1 zero_lt_one. 
Definition n2 : {x : nat | 0 < x} := exist _ 2 zero_lt_two. 

Lemma pred_strong5_test1 : pred_strong5 n1 = 0.
Proof. reflexivity. Qed.


Lemma pred_strong5_test2 : pred_strong5 n2 = 1.
Proof. reflexivity. Qed.

(*
Extraction pred_strong5.
pred_strong5 :: Nat -> Nat
pred_strong5 n = case n of 
    O   -> error "absurd case"
    S n -> n
*)

Definition pred_strong6 (n : {n : nat | 0 < n}) : {m : nat | S m = proj1_sig n} :=
    match n return {m : nat | S m = proj1_sig n} with
    | exist _  0 p      => match zltz p with end
    | exist _ (S m) _   => exist _ m (eq_refl _)
    end. 

(*
Compute (pred_strong6 (exist _ 2 zero_lt_two)).
    = exist (fun m : nat => S m = proj1_sig (exist (lt 0) 2 zero_lt_two)) 1 eq_refl
                  : {m : nat | S m = proj1_sig (exist (lt 0) 2 zero_lt_two)}
*)

(*
Extraction pred_strong6.
pred_strong6 :: Nat -> Nat
pred_strong6 n = case n of 
    O   -> error "absurd case"
    S n -> n
*)



Definition pred_strong7 : forall (n:nat), 0 < n -> {m:nat|n = S m}.
Proof.
    intros n p. destruct n.
    - apply False_rec. inversion p. 
    - exact (exist _ n eq_refl).
Qed. (* 'Qed' will hide the details of the 'proof' and make things 'opaque' *)

(*
Print pred_strong7.
*)

(* Despite opacity, can still manage to check things, but not as simple *)
Lemma pred_strong7_test : proj1_sig (pred_strong7 2 zero_lt_two) = 1.
Proof. 
    remember (pred_strong7 2 zero_lt_two) as x eqn:E. 
    destruct x as [n H]. simpl. inversion H.
    reflexivity.
Qed. 

(*
Extraction pred_strong7.
Warning: The extraction is currently set to bypass opacity, the following
opaque constant bodies have been accessed : pred_strong7.
     [extraction-opaque-accessed,extraction]
pred_strong7 :: Nat -> Nat
pred_strong7 n = case n of 
    O       -> false_rec
    S n     -> n
*)

Definition pred_strong8 : forall (n:nat), 0 < n -> {m:nat|n = S m}.
Proof.
    intros n p. destruct n.
    - apply False_rec. inversion p. 
    - exact (exist _ n eq_refl).
Defined. (* use 'Defined' rather than 'Qed' *)


(* Without opacity, checking is trivial *) 
Lemma pred_strong8_test : proj1_sig (pred_strong8 2 zero_lt_two) = 1.
Proof. reflexivity. Qed.

(*
(* no error but name pred_strong9 not in environment... *)
Program Definition pred_strong9 (n:nat) (_:0 < n) : {m:nat|n = S m} :=
    match n with
    | 0     => _
    | S n   => n
    end.
*)

(* The above was a lot simpler than this *)
Definition pred_strong10 (n:nat) (p:0 < n) : {m:nat|n = S m} :=
    (match n return (0 < n) -> {m:nat|n = S m} with
    | 0     => (fun q  => match zltz q with end)
    | S m   => (fun q  => exist _ m (eq_refl _))
    end) p.


Lemma pred_strong10_test : proj1_sig (pred_strong10 2 zero_lt_two) = 1.
Proof. reflexivity. Qed.



