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


Theorem at_least_28: forall (leap:bool)(m:month), 28 <= month_length leap m. 
Proof.
  intros leap m. case m; simpl; auto. case leap; auto.
Qed.


Print at_least_28.
(*
fun (leap : bool) (m : month) =>
match m as m0 return (28 <= month_length leap m0) with
| January => le_S 28 30 (le_S 28 29 (le_S 28 28 (le_n 28)))
| February =>
    if leap as b return (28 <= (if b then 29 else 28))
      then le_S 28 28 (le_n 28)
      else le_n 28
| March => le_S 28 30 (le_S 28 29 (le_S 28 28 (le_n 28)))
| April => le_S 28 29 (le_S 28 28 (le_n 28))
| May => le_S 28 30 (le_S 28 29 (le_S 28 28 (le_n 28)))
| June => le_S 28 29 (le_S 28 28 (le_n 28))
| July => le_S 28 30 (le_S 28 29 (le_S 28 28 (le_n 28)))
| August => le_S 28 30 (le_S 28 29 (le_S 28 28 (le_n 28)))
| September => le_S 28 29 (le_S 28 28 (le_n 28))
| October => le_S 28 30 (le_S 28 29 (le_S 28 28 (le_n 28)))
| November => le_S 28 29 (le_S 28 28 (le_n 28))
| December => le_S 28 30 (le_S 28 29 (le_S 28 28 (le_n 28)))
end
*)

Definition next_month (m:month) :=
  match m with
  | January => February | February  => March      | March     => April
  | April   => May      | May       => June       | June      => July
  | July    => August   | August    => September  | September => October 
  | October => November | November  => December   | December  => January
end.

Theorem next_august_then_july : forall m:month, 
  next_month m = August -> m = July.
Proof.
  intro m. case m; simpl; intro Hnext_eq; discriminate Hnext_eq || reflexivity. 
Qed.

Check I. (* I: True *)

Theorem not_January_eq_February : January <> February.
Proof. 
  unfold not. intros H.
  pose (g:=(fun (m:month) => match m with January => True | _ => False end)). (* can also define g from month_rec *)
  change (g February). rewrite <- H. simpl. apply I.
Qed.

Theorem not_true_eq_false : true <> false.
Proof. 
  unfold not. intro H. pose (g:= fun (b:bool) => match b with false => False | true => True end).
  change (g false). rewrite <- H. simpl. apply I.
Qed.

Theorem next_march_shorter : forall (leap:bool)(m1 m2:month), 
  next_month m1 = March -> month_length leap m1 <= month_length leap m2.  
Proof.
  intros leap m1 m2 H.
  case m1. (* we are stuck *)
  Restart.
  intros leap m1 m2.
  case m1; simpl; (discriminate || (* cannot be handled by discriminate *)
    simpl; case m2; simpl; case leap; auto).
  Restart.
  intros leap m1 m2 H. generalize H. (* then can proceed with 'case' *)
  Restart.
(* negative argument to specifiy which occurence of m1 should not be replaced in abstraction *) 
  intros leap m1 m2 H. generalize (eq_refl m1). pattern m1 at -1. 
  case m1; intro H0; rewrite H0 in H; simpl in H; (discriminate || (* case which cannot be handled with discriminate *) 
    simpl; case leap; case m2; simpl; auto).  
Qed.


Ltac caseEq f := (* our first tactic definition *)
  generalize (eq_refl f); pattern f at -1; case f.



Theorem next_march_shorter' : forall (leap:bool)(m1 m2:month), 
  next_month m1 = March -> month_length leap m1 <= month_length leap m2.  
Proof.
  intros leap m1 m2 H.
  caseEq m1; intro H'; rewrite H' in H; simpl in H; try (discriminate H).
  case leap; simpl; case m2; simpl; auto.
Qed.






