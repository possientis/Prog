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

(* another functor *)
Module PairKey (K1:KEY)(K2:KEY) : KEY with Definition 
  A := prod K1.A K2.A.
Open Scope type_scope.
  Definition A:= K1.A*K2.A.
  Definition eqdec : forall a b:A, {a = b}+{a <> b}.
    intros a b. destruct a. destruct b. elim (K1.eqdec a a1).
      intro H1. elim (K2.eqdec a0 a2).
        intro H2. left. rewrite H1, H2. reflexivity.
        intro H2. clear H1. right. unfold not. intro H3. injection H3.
          clear H3. intros H3 H4. apply H2. exact H3.
      intro H1. right. unfold not. intro H2. injection H2.
        intros H3 H4. apply H1. exact H4.
  Defined.
End PairKey.

(* now applying functor *)
Module ZZKey := PairKey ZKey ZKey.



Check (ZZKey.eqdec (5, (-8))((2+3), ((-2)*4))).

(*
Check (ZZKey.eqdec (5, (-8))((2+3), ((-2)*4)))
*)

Module BoolKey.
  Definition A:= bool.
  Definition eqdec : forall a b:A, {a = b}+{a <> b}.
    destruct a; destruct b; auto; right; discriminate.
  Defined.
End BoolKey.


Module BoolKeys : KEY with Definition A := list bool
                := LKey BoolKey.

Check (BoolKeys.eqdec (cons true nil)
(cons true (cons false nil))).
(*
BoolKeys.eqdec (true :: nil) (true :: false :: nil)
     : {true :: nil = true :: false :: nil} +
              {true :: nil <> true :: false :: nil}
*)










