(* Print unit. *)

(*
Inductive unit : Set :=  tt : unit
*)


(* Print True. *)

(*
Inductive True : Prop :=  I : True
*)

(* it would seem that the types unit and True are isomorphic *)

Definition toUnit (x:True) : unit := tt.

Definition toTrue (x:unit) : True := I.

Lemma check1 : forall (x:True), toTrue (toUnit x) = x.
Proof. intros x. unfold toTrue. destruct x. reflexivity. Qed.

Lemma check2 : forall (x:unit), toUnit (toTrue x) = x.
Proof. intros x. unfold toUnit. destruct x. reflexivity. Qed.


Definition unitToBool (x:unit) : bool :=
    match x with
    | tt            => true
    end.

Lemma check3 : forall (x:unit), unitToBool x = true.
Proof. intros x. destruct x. reflexivity. Qed.


Definition TrueToBool (x:True) : bool :=
    match x with
    | I             => true
    end.

Lemma check4 : forall (x:True), TrueToBool x = true.
Proof. intros x. destruct x. reflexivity. Qed.



