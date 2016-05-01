(* Set Implicit Arguments.*)

Require Import ZArith.
Require Import List.


Inductive plane : Set :=
  | point : Z->Z-> plane.


Inductive south_west : plane -> plane -> Prop :=
  south_west_def: 
    forall a1 a2 b1 b2:Z, (a1 <= b1)%Z -> (a2 <= b2)%Z ->
      south_west (point a1 a2) (point b1 b2).

Inductive even : nat -> Prop :=
  | O_even        : even 0
  | plus_2_even   : forall n:nat, even n -> even (S (S n)).

(* curly braces '{}' indicate an implicit argument *)
Inductive sorted {A:Set}(R:A->A->Prop) : list A -> Prop :=
  | sorted0       : sorted R nil
  | sorted1       : forall x:A, sorted R (cons x nil)
  | sorted2       : forall (x y:A)(l:list A),
                      R x y -> sorted R (cons y l) -> sorted R (cons x (cons y l)).

Inductive le (n:nat) : nat -> Prop :=
  | le_n          : le n n
  | le_S          : forall m:nat, le n m -> le n (S m).


Definition relation (A:Type) := A -> A -> Prop.

(* transitive closure *)
Inductive clos_trans {A:Type}(R:relation A): A -> A -> Prop :=
  | t_step : forall x y:A, R x y -> clos_trans R x y
  | t_trans: forall x y z:A, clos_trans R x y -> clos_trans R y z
              -> clos_trans R x z.

Inductive last {A:Type} : A -> list A -> Prop :=
  | last1 : forall a:A, last a (cons a nil)
  | last2 : forall (a x:A)(l:list A), last a l -> last a (cons x l).

Fixpoint last_fun {A:Type} (l:list A) : option A :=
  match l with
    | nil           => None
    | (cons a nil)  => Some a
    | (cons a l')   => last_fun l'
  end.


Lemma last_a_l_not_nil : forall (A:Type)(a:A)(l:list A),
  last a l -> l <> nil.
Proof.
  intros A a l p. generalize p. elim p. intros b H. clear H.
  intro H. apply nil_cons with (x:=b)(l:=nil). auto.
  intros b x l' q H0 H1. clear H0 H1 q b p l a. intro H.
  apply nil_cons with (x:=x)(l:=l'). auto.
Qed.

Lemma not_last_a_nil: forall (A:Type)(a:A),
  ~last a nil.
Proof.
  intros A a H. apply last_a_l_not_nil with (l:=nil)(a:=a).
  exact H. reflexivity.
Qed.

Lemma last_coherence : forall (A:Type)(l:list A)(a:A),
  last a l <-> last_fun l = Some a.
Proof.
  (* -> *)
  intros A l a. split. intro p. generalize p. elim p.
  intros b H0. clear H0. simpl. reflexivity.
  intros b x m. case m. intro H. apply False_ind.
  apply not_last_a_nil with (a:=b). exact H.
  intros c l' H H' H''. simpl. apply H'. exact H.
  (* <- *)
  elim l. simpl. intro H. discriminate H.
  clear l. intros b l. case l. simpl. intros H H'.
  cut(a = b). intro H''. rewrite <- H''. apply last1.
  pose (g:= fun x =>  match x with | None    => a | Some c  => c end).
  change (g (Some a) = g (Some b)). rewrite H'. reflexivity.
  clear l. intros c l H H'. apply last2. apply H. rewrite <- H'.
  simpl. reflexivity.
Qed.

(* last_with_rest a l l' expresses the fact that l = l' ++ [a] 
** i.e. that a is the last element of l, and l' is what remains of
** the list after removing the last element 'a'                    *)
Inductive last_with_rest {A:Type} : A -> list A -> list A -> Prop := 
  | last_with_rest1 : forall a:A, last_with_rest a (cons a nil) nil 
  | last_with_rest2 : forall (a b:A)(l m:list A), 
      last_with_rest a l m -> last_with_rest a (cons b l) (cons b m).

Inductive palindrome {A:Type} : list A -> Prop :=
  | palindrome_nil    : palindrome nil
  | palindrome_single : forall (a:A), palindrome (cons a nil)
  | palindrome_a      : forall (a:A)(l m:list A), 
      last_with_rest a l m -> palindrome m -> palindrome (cons a l). 

Definition pal_example1 := 1::2::3::4::5::4::3::2::1::nil.
Definition pal_example2 := 1::2::2::1::nil.
Definition pal_example3 := 1::2::nil. (* not a palindrome *)

Lemma palindrome_example2: palindrome pal_example2.
Proof.
  unfold pal_example2. apply palindrome_a with (a:=1)(m:= 2::2::nil).
  repeat apply last_with_rest2. apply last_with_rest1.
  apply palindrome_a with (m:=nil). apply last_with_rest1. apply palindrome_nil.
Qed.

Lemma palindrome_example1: palindrome pal_example1.
Proof.
  unfold pal_example1.
  apply palindrome_a with (m:= 2::3::4::5::4::3::2::nil). 
  repeat apply last_with_rest2. apply last_with_rest1.
  apply palindrome_a with (m:= 3::4::5::4::3::nil). 
  repeat apply last_with_rest2. apply last_with_rest1.
  apply palindrome_a with (m:= 4::5::4::nil). 
  repeat apply last_with_rest2. apply last_with_rest1.
  apply palindrome_a with (m:= 5::nil). 
  repeat apply last_with_rest2. apply last_with_rest1.
  apply palindrome_single.
Qed.


Theorem cons_injective : forall (A : Set)(a b : A)(l m : list A),
      a :: l = b :: m -> l = m.
      intros A a b l m h.
      fold (tail (cons a l)). (* the fold trick , very handy !! *)
      rewrite h.
      unfold tail.
      reflexivity.
      Qed.

Lemma last_with_rest_last: forall (A:Type)(a:A)(l m:list A),
  last_with_rest a l m -> last a l.
Proof.
  intros A a l m H. generalize H. elim H. clear H a m l.  
  intros a H. apply last1. clear H m l a. intros a b l m.
  intros H0 H1 H2. apply last2, H1, H0.
Qed.

Lemma last_single: forall (A:Type)(a b:A),
  last a (b::nil) -> a = b.
Proof.
  intros A a b H. cut(forall l:list A, last a l -> l = b::nil -> a = b).
  intro H'. apply H' with (l:=b::nil). exact H. reflexivity. intros l Hal.
  generalize Hal. elim Hal.

(*
Lemma last_unique: forall (A:Type)(a b:A)(l:list A),
  last a l -> last b l -> a = b.
Proof.
  intros A a b l Ha. generalize b. clear b. generalize Ha. elim Ha.
  clear Ha a l. intros a Ha. clear Ha. intros b Hb. generalize Hb.
  cut (forall l:list A, l = a::nil -> last b l -> a = b). intro H.
  apply H. reflexivity. intro l. clear Hb. intros Ha Hb. generalize Hb.
  generalize Ha. elim Hb. intros c Heq H'. clear H'.
  pose (g:= fun l => match l with | nil => c | x::l' => x end).
  fold (g (c::nil)). rewrite Heq. simpl. reflexivity. clear Hb.
  clear Ha. clear l. clear b. intros b x l H IH H' H''.
*)

(*
Lemma palindrome_law : forall (A:Type) (a b:A)(l m:list A),
  palindrome l -> l = cons a m-> last b m -> a = b.
Proof.
  intros A a b l m H. generalize H. generalize a b m.
  clear a b m. elim H. intros a b m H0 H1. discriminate H1.
  intros a x b m H0 H1 H2. fold(tl (x::m)) in H2. rewrite <- H1 in H2.
  simpl in H2. apply False_ind. apply not_last_a_nil with (a:=b).
  exact H2. clear H l. intros a l m. intros H0 H1 IH x b l' H2 H3 H4.

*)

(*
Lemma palindrome_example3: ~palindrome pal_example3.
Proof.
  unfold pal_example3. intro pal. generalize pal.
  elim pal.
*)


