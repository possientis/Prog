Require Import List.
Require Import ZArith.
Require Import key.

(* Defining a functor. *)
Module LKey (K:KEY): KEY with Definition A := list K.A.
  Definition A:= list K.A.
  Definition eqdec: forall a b:A, {a = b}+{a <> b}.
    intro a. elim a.
    clear a. intro b. elim b. 
      clear b. left. reflexivity.
      clear b. intros a l H. right. unfold not. intros. discriminate.
    clear a. intros a l IH. intros b. elim b.
      clear b. right. unfold not. intros. discriminate.
      clear b. intros b m H0. clear H0. generalize (K.eqdec a b). intro H0. elim H0.
        clear H0. intro H0. generalize (IH m). intro H1. elim H1.
          clear H1. intro H1. left. rewrite H0, H1. reflexivity.
          clear H1. intro H1.  right. unfold not. intro H2. injection H2. 
          intros H3 H4. apply H1. exact H3.
        clear H0. intro H0. right. unfold not. intro H1. injection H1.
          intros H2 H3. apply H0. exact H3.
  Defined.
End LKey.
        
(* ZKey is an implementation of KEY, where definition of A is exported *)
Module ZKey : KEY with Definition A:=Z.
  Definition A:=Z.
  Definition eqdec := Z_eq_dec.
End ZKey.


(* we can create an implementation of KEY by applying functor to ZKey *)
Module LZKey := LKey ZKey.

Open Scope Z_scope.
Check (LZKey.eqdec (cons 7 nil)(cons (3+4) nil)).
(*
LZKey.eqdec (7 :: nil) (3 + 4 :: nil)
     : {7 :: nil = 3 + 4 :: nil} + {7 :: nil <> 3 + 4 :: nil}
*)

Module LLZKey := LKey LZKey.
Check (LLZKey.eqdec (cons (cons 7 nil) nil)
                    (cons (cons (3+4) nil) nil)).
(*
LLZKey.eqdec ((7 :: nil) :: nil) ((3 + 4 :: nil) :: nil)
     : {(7 :: nil) :: nil = (3 + 4 :: nil) :: nil} +
              {(7 :: nil) :: nil <> (3 + 4 :: nil) :: nil}
*)








