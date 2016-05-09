Require Import List.
Require Import Arith.

Parameter A:Type.
Parameter R: A -> A -> Prop.
Parameter R_bool: A -> A -> bool.
Axiom R_refl:   forall x:A, R x x.
Axiom R_anti:   forall x y:A, R x y -> R y x -> x = y.
Axiom R_trans:  forall x y z:A, R x y -> R y z -> R x z.
Axiom R_total:  forall x y:A, R x y \/ R y x.
Axiom R_lem:    forall x y:A, R x y <-> R_bool x y = true.


Fixpoint sort_n (n:nat): list A -> list A :=
  match n with
    | 0   => (fun _ => nil)
    | S p => (fun l =>
      match l with
        | nil       =>  nil
        | (x::nil)  =>  (x::nil)
        | (x::l')   =>  let m := sort_n p l' in
                        let y := hd_error m  in
                        match y with
                          | None    => nil (* should not happen *)
                          | Some z  => match R_bool x z with
                                        | true  =>  (x::m)
                                        | false =>  let m' := tl m in
                                                    z::sort_n p (x::m') 
                                       end
                        end
      end)
  end. 

(* This lemma is part of the Coq 8.5 library *)
Lemma length_zero_iff_nil : forall (A:Type) (l:list A),
  length l = 0 <-> l = nil.
Proof.
  intros A l. elim l. unfold length. split; auto. 
  clear l. intros a l H. split. clear H. simpl. intro H.
  discriminate H. clear H. intro H. discriminate H.
Qed.



Lemma sort_n_Sn : forall (n:nat) (l:list A),
  length l <= n -> sort_n n l = sort_n (S n) l.
Proof.
  (* induction on n *)
  intros n. elim n.
  (* n = 0 *)
  intros l H. cut (l = nil). intro H'. rewrite H'. simpl. reflexivity.
  apply length_zero_iff_nil. symmetry. apply le_n_0_eq. exact H.
  (* n -> n+1 *)(* induction on l *)
  clear n. intros n IH l. elim l.
  (* l = nil *)
  simpl. auto.
  (* l = (x::l') *)(* induction on l' *)
  clear l. intros x l' H. clear H. elim l'.
  (* l' = nil *)
  simpl. auto.
  (* l' = (a::l'') *)
  clear l'. intros a l'' H. clear H. intro H.
  pose (p:= S n). change (sort_n (S n) (x :: a :: l'') = sort_n (S p) (x :: a :: l'')).
  unfold sort_n at 2. fold sort_n. unfold p. symmetry. rewrite <- IH, <- IH.
  symmetry. unfold sort_n at 1. fold sort_n. reflexivity.
  simpl.



