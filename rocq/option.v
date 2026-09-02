Set Implicit Arguments.
Require Import Arith.
Require Import List.

Print option.
(* Inductive option (A : Type) : Type :=  
    | Some : A -> option A 
    | None : option A 
*)

Definition pred_option (n:nat) : option nat :=
  match n with
    | 0         => None
    | S p       => Some p
  end.

Eval compute in pred_option 0.
Eval compute in pred_option 345.

Definition pred2_option (n:nat) : option nat :=
  match pred_option n with 
    | None      => None
    | Some p    => pred_option p
  end.

Eval compute in pred2_option 0.
Eval compute in pred2_option 1.
Eval compute in pred2_option 2.
Eval compute in pred2_option 345.

Fixpoint nth_option (A:Type)(n:nat)(l:list A) : option A :=
  match n, l with (* match applied to a pair *)
    | 0,    cons a ls => Some a
    | S p,  cons a ls => nth_option p ls
    | n,    nil       => None
  end. 

Fixpoint nth_option' (A:Type)(n:nat)(l:list A) : option A :=
  match n with 
    | 0       => match l with
                  | nil       => None
                  | cons a ls => Some a
                end
    | S p     => match l with
                  | nil       => None
                  | cons a ls => nth_option' p ls
                end
  end.

Lemma nth_option_equiv : forall (A:Type)(n:nat)(l:list A),
  nth_option n l = nth_option' n l.
Proof.
  intros A n. elim n. intro l. elim l. simpl. reflexivity.
  intros a ls IH. clear IH. simpl. reflexivity. clear n. intro n.
  intros IH l. elim l. simpl. reflexivity. clear l. intros a ls H.
  simpl. apply IH.
Qed.

Lemma L1: forall (A:Type)(n:nat)(l:list A),
  nth_option n l = None -> length l <= n.
Proof.
  intros A n. elim n. intro l. elim l. simpl. trivial.
  clear l. intros a ls IH. simpl. intro H. discriminate H. clear n.
  intros n IH l. elim l. simpl. intro H. apply le_0_n.
  clear l. intros a ls. intro H. simpl. clear H. intro H.
  apply le_n_S. apply IH. exact H.
Qed.

Fixpoint filter (A:Type)(P:A -> bool)(l:list A) : list A :=
  match l with
    | nil       => nil
    | cons a ls => let fs := filter P ls in if P a then cons a fs else fs
  end.

Fixpoint even (n:nat) : bool :=
  match n with 
    | 0       => true
    | S 0     => false
    | S (S n) => even n
  end.

Eval compute in filter even (0::1::2::3::4::5::6::7::8::9::10::nil).







