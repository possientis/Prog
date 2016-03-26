Set Implicit Arguments.



Print bool. (* Inductive bool : Set :=  true : bool | false : bool *)

Inductive month : Set := 
  | January : month | February : month  | March : month
  | April : month   | May : month       | June : month
  | July : month    | August : month    | September : month
  | October : month | November : month  | December : month.



Inductive whatever : Set := | A | B | C | D. (* simpler syntax *)

Check month_ind.
(*
forall P : month -> Prop,
       P January ->
       P February ->
       P March ->
       P April ->
       P May ->
       P June ->
       P July ->
       P August ->
       P September ->
       P October -> P November -> P December -> forall m : month, P m
*)

Check month_rec.
(*
forall P : month -> Set,
       P January ->
       P February ->
       P March ->
       P April ->
       P May ->
       P June ->
       P July ->
       P August ->
       P September ->
       P October -> P November -> P December -> forall m : month, P m
*)

Inductive season : Set :=
  | Spring : season
  | Summer : season
  | Autumn : season
  | Winter : season.

Definition month_to_season : month -> season :=
  month_rec (fun m => season)
            Winter Winter Spring
            Spring Spring Summer
            Summer Summer Autumn
            Autumn Autumn Winter.

Eval compute in month_to_season January.
Eval compute in month_to_season February.
Eval compute in month_to_season March.
Eval compute in month_to_season April.
Eval compute in month_to_season May.
Eval compute in month_to_season June.
Eval compute in month_to_season July.
Eval compute in month_to_season August.
Eval compute in month_to_season September.
Eval compute in month_to_season October.
Eval compute in month_to_season November.
Eval compute in month_to_season December.

Check bool_ind. (* forall P : bool -> Prop, P true -> P false -> forall b : bool, P b *)
Check bool_rec. (* forall P : bool -> Set, P true -> P false -> forall b : bool, P b  *)
Check bool_rect. (* forall P : bool -> Type, P true -> P false -> forall b : bool, P b *)

Theorem month_equal : forall m:month,
  m=January \/ m=February \/ m=March      \/ m=April    \/ m=May      \/ m=June \/
  m=July    \/ m=August   \/ m=September  \/ m=October  \/ m=November \/ m=December.
Proof.
  induction m; auto 12.
Qed.

Reset month_equal.

Theorem month_equal : forall m:month,
  m=January \/ m=February \/ m=March      \/ m=April    \/ m=May      \/ m=June \/
  m=July    \/ m=August   \/ m=September  \/ m=October  \/ m=November \/ m=December.
Proof.
  intro m. pattern m. apply month_ind; auto 12. (* 12 sub-goals *)
Qed.


Check or_introl. (* forall A B : Prop, A -> A \/ B *)
Check or_intror. (* forall A B : Prop, B -> A \/ B *)
Check refl_equal(A:=Type).  (* forall x : Type, x = x *)
Check eq_refl(A:=Type).     (* forall x : Type, x = x *)
Check bool_ind. (* forall P : bool -> Prop, P true -> P false -> forall b : bool, P b *)

Theorem bool_equal: forall b:bool, b = true \/ b = false.
Proof.
  intro b. pattern b. apply bool_ind. apply or_introl. apply eq_refl.
  apply or_intror. apply eq_refl.
Qed.

Print bool_equal.
(*
fun b : bool =>
  bool_ind  (fun b0 : bool => b0 = true \/ b0 = false) 
            (or_introl eq_refl) 
            (or_intror eq_refl) b

  : forall b : bool, b = true \/ b = false
*)

Reset bool_equal.

Theorem bool_equal: forall b:bool, b = true \/ b = false.
Proof.
  exact(fun b : bool => 
          bool_ind  (fun b0 : bool => b0 = true \/ b0 = false) 
                    (or_introl (true = false) (eq_refl true)) 
                    (or_intror (false = true) (eq_refl false)) 
                    b).
Qed. 

Check or_introl (true = false) (eq_refl true).  (*  true = true \/ true = false *) 
Check or_intror (false = true) (eq_refl false). (* false = true \/ false = false *)

Reset bool_equal.

Theorem bool_equal: forall b:bool, b = true \/ b = false.
Proof.
  intro b. pattern b. apply bool_ind. left. reflexivity. right. reflexivity.
Qed.

Check (fun b:bool => match b with true => 33 | false => 45 end). 
(*
fun b : bool => if b then 33 else 45
       : bool -> nat
*)

Definition month_length (leap:bool)(m:month) : nat :=
  match m with
  | January => 31 | February  => if leap then 29 else 28
  | March   => 31 | April     => 30   | May => 31 | June  => 30
  | July    => 31 | August    => 31   | September => 30
  | October => 31 | November  => 30   | December  => 31
  end.
(*
Definition month_length2 : bool->month->nat :=
 fun (leap:bool)(m:month) => match m with January => 31 end.
Error: Non exhaustive pattern-matching: no clause found for pattern February
*)

Check month_rec.
(*
forall P : month -> Set,
       P January ->
       P February ->
       P March ->
       P April ->
       P May ->
       P June ->
       P July ->
       P August ->
       P September ->
       P October -> P November -> P December -> forall m : month, P m
*)

Definition month_length' (leap:bool) :=
  month_rec (fun m:month => nat)
  31 (if leap then 29 else 28) 31 30 31 30 31 31 30 31 30 31.

Print month_length.
Print month_length'.

Definition month_length'' (leap:bool) (m:month) : nat :=
  match m with
  | February  => if leap then 29 else 28
  | April => 30 | June  => 30 | September => 30 | November  => 30
  | other  => 31 (* lower case indicates variable name *)
  end.

Eval compute in (fun leap => month_length leap November).
(* fun _ : bool => 30
   : bool -> nat
*)

Theorem length_february : month_length false February = 28.
Proof.
  simpl. (* triggers iota reduction *)
  reflexivity.
Qed.




Definition month_even (leap:bool)(m:month) : bool :=
  match (month_length leap m) with
    | 28    => true 
    | 29    => false
    | 30    => true
    | 31    => false
    | other => false 
  end.

Definition bool_xor (b1:bool)(b2:bool) : bool :=
  match (b1,b2) with
  | (true, true)    => false
  | (true, false)   => true
  | (false, true)   => true
  | (false, false)  => false
  end.

Definition bool_and (b1:bool)(b2:bool) : bool :=
  match (b1,b2) with
  | (true, true)    => true
  | (true, false)   => false
  | (false, true)   => false
  | (false, false)  => false
  end.

Definition bool_or (b1:bool)(b2:bool) : bool :=
  match (b1,b2) with
  | (true, true)    => true
  | (true, false)   => true
  | (false, true)   => true
  | (false, false)  => false
  end.

Definition bool_eq (b1:bool)(b2:bool) : bool :=
  match (b1,b2) with
  | (true, true)    => true
  | (true, false)   => false
  | (false, true)   => false
  | (false, false)  => true
  end.

Definition bool_not (b:bool): bool :=
  match b with
  | true  => false
  | false => true
  end.

Theorem xor_not_eq : forall b1 b2:bool, bool_xor b1 b2 = bool_not (bool_eq b1 b2).
Proof.
  intros x y. pattern x; apply bool_ind; pattern y; apply bool_ind; reflexivity.
Qed.


Theorem not_and_or : forall x y: bool, 
  bool_not(bool_and x y) = bool_or (bool_not x)(bool_not y).
Proof.
  intros x y. elim x; elim y; reflexivity.
Qed.

Theorem not_not : forall b:bool, bool_not (bool_not b) = b.
Proof.
  intro x. elim x; reflexivity. 
Qed.

Theorem bool_lem : forall b:bool, bool_or b (bool_not b) = true.
Proof.
  intro x. elim x; reflexivity.
Qed.

Theorem eq_eq : forall x y:bool, bool_eq x y = true -> x = y.
Proof.
  intros x y. elim x; elim y; intro H; unfold bool_eq in H; auto.
Qed.

Theorem eq_eq_rev : forall x y:bool, x = y -> bool_eq x y = true.
Proof.
  intros x y H. rewrite H. elim y; reflexivity.
Qed.

Theorem not_or_and_not : forall x y:bool,
  bool_not (bool_or x y) = bool_and (bool_not x) (bool_not y).
Proof.
  intros x y. elim x; elim y; reflexivity.
Qed.

Theorem distr : forall x y z: bool,
  bool_or (bool_and x z) (bool_and y z) = bool_and (bool_or x y) z.
Proof.
  intros x y z. elim x; elim y; elim z; reflexivity.
Qed.










