Inductive eList (a:Set) : Set :=
| Nil   : eList a
| ECons : a -> oList a -> eList a
with oList (a:Set) : Set :=
| OCons : a -> eList a -> oList a
.

Arguments Nil {a}.
Arguments ECons {a} _ _.
Arguments OCons {a} _ _.

Fixpoint eLength (a:Set) (xs:eList a) : nat :=
    match xs with
    | Nil           => O
    | ECons _ xs    => S (oLength a xs)
    end
with oLength (a:Set) (xs:oList a) : nat :=
    match xs with 
    | OCons _ xs    => S (eLength a xs)
    end
.

Arguments eLength {a} _.
Arguments oLength {a} _.

Fixpoint eeAppend (a:Set) (xs ys:eList a) : eList a :=
    match xs with
    | Nil           => ys
    | ECons x xs    => ECons x (oeAppend a xs ys)
    end
with oeAppend (a:Set) (xs : oList a) (ys:eList a) : oList a :=
    match xs with
    | OCons x xs => OCons x (eeAppend a xs ys)
    end
.    

Fixpoint ooAppend (a:Set) (xs ys:oList a) : eList a :=
    match xs with
    | OCons x xs    => ECons x (eoAppend a xs ys)
    end
with eoAppend (a:Set) (xs:eList a) (ys:oList a) : oList a :=
    match xs with 
    | Nil           => ys
    | ECons x xs    => OCons x (ooAppend a xs ys)
    end
.

Arguments eeAppend {a} _ _.
Arguments eoAppend {a} _ _.
Arguments oeAppend {a} _ _.
Arguments ooAppend {a} _ _.

(* generate mutual induction scheme *)
Scheme eList_mut := Induction for eList Sort Prop
with oList_mut := Induction for oList Sort Prop.

(*
Check eList_mut.

eList_mut : 
    forall (a : Set) (P : eList a -> Prop) (Q : oList a -> Prop),
    P Nil ->
    (forall (x : a) (xs : oList a), Q xs -> P (ECons x xs)) ->
    (forall (x : a) (xs : eList a), P xs -> Q (OCons x xs)) ->
    forall (xs : eList a), P xs
*)

(*
Check oList_mut.

oList_mut : 
    forall (a : Set) (P : eList a -> Prop) (Q : oList a -> Prop),
    P Nil ->
    (forall (x : a) (xs : oList a), Q xs -> P (ECons x xs)) ->
    (forall (x : a) (xs : eList a), P xs -> Q (OCons x xs)) ->
    forall (xs : oList a), Q xs
*)

Lemma plus_n_O': forall (n:nat), plus n 0 = n.
Proof. 
    apply nat_ind; simpl.
    - reflexivity.
    - intros n IH. rewrite IH. reflexivity.
Qed.

Lemma plus_n_O'': forall (n:nat), plus n 0 = n.
Proof.
    apply (nat_ind (fun n => plus n 0 = n)); simpl.
    - reflexivity.
    - intros n IH. rewrite IH. reflexivity.
Qed.
    
Lemma length_eeAppend : forall (a:Set) (xs ys:eList a),
    eLength (eeAppend xs ys) = plus (eLength xs) (eLength ys).
Proof.
    intros a. 
    apply (eList_mut a 
        (fun (xs:eList a) => forall (ys:eList a), 
            eLength (eeAppend xs ys) = plus (eLength xs) (eLength ys))
        (fun (xs:oList a) => forall (ys:eList a),
            oLength (oeAppend xs ys) = plus (oLength xs) (eLength ys))).
    - reflexivity.
    - intros x xs IH ys. simpl. rewrite IH. reflexivity.
    - intros x xs IH ys. simpl. rewrite IH. reflexivity.
Qed.

Lemma length_eoAppend : forall (a:Set) (xs:eList a) (ys:oList a),
    oLength (eoAppend xs ys) = plus (eLength xs) (oLength ys).
Proof.
    intros a.
    apply (eList_mut a 
        (fun (xs:eList a) => forall (ys:oList a), 
            oLength (eoAppend xs ys) = plus (eLength xs) (oLength ys))
        (fun (xs:oList a) => forall (ys:oList a),
            eLength (ooAppend xs ys) = plus (oLength xs) (oLength ys))).
    - reflexivity.
    - intros x xs IH ys. simpl. rewrite IH. reflexivity.
    - intros x xs IH ys. simpl. rewrite IH. reflexivity.
Qed.

Lemma length_oeAppend : forall (a:Set) (xs:oList a) (ys:eList a),
    oLength(oeAppend xs ys) = plus (oLength xs) (eLength ys).
Proof.
    intros a.
    apply (oList_mut a 
        (fun (xs:eList a) => forall (ys:eList a), 
            eLength (eeAppend xs ys) = plus (eLength xs) (eLength ys))
        (fun (xs:oList a) => forall (ys:eList a),
            oLength (oeAppend xs ys) = plus (oLength xs) (eLength ys))).
    - reflexivity.
    - intros x xs IH ys. simpl. rewrite IH. reflexivity.
    - intros x xs IH ys. simpl. rewrite IH. reflexivity.
Qed.



Lemma length_ooAppend : forall (a:Set) (xs:oList a) (ys:oList a),
    eLength(ooAppend xs ys) = plus (oLength xs) (oLength ys).
Proof.
    intros a.
    apply (oList_mut a 
        (fun (xs:eList a) => forall (ys:oList a), 
            oLength (eoAppend xs ys) = plus (eLength xs) (oLength ys))
        (fun (xs:oList a) => forall (ys:oList a),
            eLength (ooAppend xs ys) = plus (oLength xs) (oLength ys))).
    - reflexivity.
    - intros x xs IH ys. simpl. rewrite IH. reflexivity.
    - intros x xs IH ys. simpl. rewrite IH. reflexivity. 
Qed.

Fixpoint test0 (n:nat) : nat := 
    match n with
    | 0     => 0
    | S n   => test1 n
    end
with test1 (n:nat) : nat := 
    match n with
    | 0     => 0
    | S n   => test2 n
    end
with test2 (n:nat) : nat :=
    match n with 
    | 0     => 0
    | S n   => test3 n
    end
with test3 (n:nat) : nat :=
    match n with
    | 0     => 0
    | S n   => test0 n
    end.

Lemma test_all : test0 7 = 0.
Proof. reflexivity. Qed.



(*
Check eList_mut.

eList_mut : 
    forall (a : Set) (P : eList a -> Prop) (Q : oList a -> Prop),
    P Nil ->
    (forall (x : a) (xs : oList a), Q xs -> P (ECons x xs)) ->
    (forall (x : a) (xs : eList a), P xs -> Q (OCons x xs)) ->
    forall (xs : eList a), P xs
*)

(*
Check oList_mut.

oList_mut : 
    forall (a : Set) (P : eList a -> Prop) (Q : oList a -> Prop),
    P Nil ->
    (forall (x : a) (xs : oList a), Q xs -> P (ECons x xs)) ->
    (forall (x : a) (xs : eList a), P xs -> Q (OCons x xs)) ->
    forall (xs : oList a), Q xs
*)

(* We can build these induction principle manually *)
(* First we define the general recursion principle *)
Fixpoint eList_mut_rect (a:Set)(P:eList a -> Type)(Q:oList a -> Type)
    (pnil : P Nil)
    (p:forall (x:a)(xs:oList a), Q xs -> P (ECons x xs))
    (q:forall (x:a)(xs:eList a), P xs -> Q (OCons x xs))
    (xs:eList a)
    : P xs :=
        match xs with
        | Nil           => pnil
        | ECons x xs    => p x xs (oList_mut_rect a P Q pnil p q xs)
        end
with oList_mut_rect (a:Set)(P:eList a -> Type)(Q:oList a -> Type)
    (pnil : P Nil)
    (p:forall (x:a)(xs:oList a), Q xs -> P (ECons x xs))
    (q:forall (x:a)(xs:eList a), P xs -> Q (OCons x xs))
    (xs:oList a)
    : Q xs :=
        match xs with
        | OCons x xs    => q x xs (eList_mut_rect a P Q pnil p q xs)
        end
.

(* We can specialize this recursion principle to Prop *) 

Definition eList_mut_ind (a:Set)(P:eList a -> Prop)(Q:oList a -> Prop)
    (pnil: P Nil)
    (p:forall (x:a)(xs:oList a), Q xs -> P (ECons x xs))
    (q:forall (x:a)(xs:eList a), P xs -> Q (OCons x xs))
    (xs:eList a)
    : P xs := eList_mut_rect a P Q pnil p q xs.

Definition oList_mut_ind (a:Set)(P:eList a -> Prop)(Q:oList a -> Prop)
    (pnil: P Nil)
    (p:forall (x:a)(xs:oList a), Q xs -> P (ECons x xs))
    (q:forall (x:a)(xs:eList a), P xs -> Q (OCons x xs))
    (xs:oList a)
    : Q xs := oList_mut_rect a P Q pnil p q xs.

(* we can now prove all four concatenation lemmas using those *)

Lemma length_eeAppend' : forall (a:Set) (xs ys:eList a),
    eLength (eeAppend xs ys) = plus (eLength xs) (eLength ys).
Proof.
    intros a. 
    apply (eList_mut_ind a 
        (fun (xs:eList a) => forall (ys:eList a), 
            eLength (eeAppend xs ys) = plus (eLength xs) (eLength ys))
        (fun (xs:oList a) => forall (ys:eList a),
            oLength (oeAppend xs ys) = plus (oLength xs) (eLength ys))).
    - reflexivity.
    - intros x xs IH ys. simpl. rewrite IH. reflexivity.
    - intros x xs IH ys. simpl. rewrite IH. reflexivity.
Qed.


Lemma length_eoAppend' : forall (a:Set) (xs:eList a) (ys:oList a),
    oLength (eoAppend xs ys) = plus (eLength xs) (oLength ys).
Proof.
    intros a.
    apply (eList_mut_ind a 
        (fun (xs:eList a) => forall (ys:oList a), 
            oLength (eoAppend xs ys) = plus (eLength xs) (oLength ys))
        (fun (xs:oList a) => forall (ys:oList a),
            eLength (ooAppend xs ys) = plus (oLength xs) (oLength ys))).
    - reflexivity.
    - intros x xs IH ys. simpl. rewrite IH. reflexivity.
    - intros x xs IH ys. simpl. rewrite IH. reflexivity.
Qed.

Lemma length_oeAppend' : forall (a:Set) (xs:oList a) (ys:eList a),
    oLength(oeAppend xs ys) = plus (oLength xs) (eLength ys).
Proof.
    intros a.
    apply (oList_mut_ind a 
        (fun (xs:eList a) => forall (ys:eList a), 
            eLength (eeAppend xs ys) = plus (eLength xs) (eLength ys))
        (fun (xs:oList a) => forall (ys:eList a),
            oLength (oeAppend xs ys) = plus (oLength xs) (eLength ys))).
    - reflexivity.
    - intros x xs IH ys. simpl. rewrite IH. reflexivity.
    - intros x xs IH ys. simpl. rewrite IH. reflexivity.
Qed.



Lemma length_ooAppend' : forall (a:Set) (xs:oList a) (ys:oList a),
    eLength(ooAppend xs ys) = plus (oLength xs) (oLength ys).
Proof.
    intros a.
    apply (oList_mut_ind a 
        (fun (xs:eList a) => forall (ys:oList a), 
            oLength (eoAppend xs ys) = plus (eLength xs) (oLength ys))
        (fun (xs:oList a) => forall (ys:oList a),
            eLength (ooAppend xs ys) = plus (oLength xs) (oLength ys))).
    - reflexivity.
    - intros x xs IH ys. simpl. rewrite IH. reflexivity.
    - intros x xs IH ys. simpl. rewrite IH. reflexivity. 
Qed.

Fixpoint factorial (n:nat) : nat :=
    match n with
    | 0     => 1
    | S n   => mult (S n) (factorial n)
    end.

Lemma factorial_test : factorial 5 = 120.
Proof. reflexivity. Qed.

Definition factorial' : nat -> nat := 
    fix f (n:nat) : nat := 
        match n with
        | 0     => 1
        | S n   => mult (S n) (f n)
        end.

Lemma factorial_test' : factorial' 5 = 120.
Proof. reflexivity. Qed.

Lemma factorial_same : forall (n:nat), factorial n = factorial' n.
Proof.
    induction n as [|n IH]; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
Qed.



