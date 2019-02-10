Inductive eList (a:Set) : Set :=
| Nil   : eList a
| ECons : a -> oList a -> eList a
with oList (a:Set) : Set :=
| OCons : a -> eList a -> oList a
.

Arguments Nil {a}.
Arguments ECons {a}.
Arguments OCons {a}.

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

Arguments eLength {a}.
Arguments oLength {a}.

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

Arguments eeAppend {a}.
Arguments eoAppend {a}.
Arguments oeAppend {a}.
Arguments ooAppend {a}.

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


