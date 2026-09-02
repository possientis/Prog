Require Import Arith. (* arith tactic DB *)
Require Import divide.

Ltac autoClear h := try (clear h; auto with arith; fail).

Ltac autoAfter tac := try(tac; auto with arith; fail).


Lemma example_use1: forall n p: nat, 
  n < p -> n <= p -> 0 < p -> S n < S p.
Proof.
  intros n p H H0 H1. autoAfter ltac:(clear H0 H1). (* clear H0 H1. auto with arith. *)
Qed.

Ltac le_S_star := apply le_n || (apply le_S; le_S_star). (* tactice is recursive *)


Theorem le_5_25: 5 <= 25.
Proof.
  le_S_star.  
Qed.

Ltac check_not_divides :=
  match goal with
    | [ |- (~divides ?X1 ?X2) ] => 
        cut (X1 <= X2); [idtac | le_S_star]; intros Hle;
        rewrite (le_plus_minus _ _ Hle); apply not_divides_plus;
        simpl; clear Hle; check_not_divides (* recursive call *)
    | [ |- _ ]                  => apply not_divides_lt; unfold lt; le_S_star
  end.

Lemma check1: ~divides 34 45.
Proof.
  match goal with
    | [ |- (~divides ?X1 ?X2) ] =>
      cut(X1 <= X2); [idtac | le_S_star]; intro Hle; rewrite (le_plus_minus _ _ Hle);
    apply not_divides_plus; simpl; clear Hle; check_not_divides
    | [  |- _]                  =>
      apply not_divides_lt; unfold lt; le_S_star 
  end.
Qed.


Lemma check2: ~divides 34 45.
Proof.
  check_not_divides.
Qed.


Ltac contrapose H :=
  match goal with
    | [id:(~_) |- (~_)] => intro H; apply id
  end.

Theorem  example_contrapose :
  forall x y:nat, x<>y -> x <= y-> ~y<=x.
Proof.
  intros x y H H0. contrapose H'. auto with arith.
Qed.

Ltac check_lt_not_divides :=
  match goal with
    | [Hlt:(lt ?X1 2%nat) |- (~divides ?X1 ?X2) ] =>
      apply not_lt_2_divides; auto
    | [Hlt:(lt ?X1 ?X2) |- (~divides ?X1 ?X3) ]   =>
      elim (lt_lt_or_eq _ _ Hlt);
      [clear Hlt; intros Hlt; check_lt_not_divides
      | intros Heq; rewrite Heq; check_not_divides]
  end.

Definition is_prime: nat -> Prop :=
  fun p:nat => forall n:nat, n <> 1 -> lt n p -> ~divides n p.

Hint Resolve lt_0_Sn.

(* time consuming ..

Theorem prime37 : is_prime 37.
Proof.
  Time(unfold is_prime; intros; check_lt_not_divides).
Qed.

Theorem prime61 : is_prime 61.
Proof.
  Time(unfold is_prime; intros; check_lt_not_divides).
Qed.
*)


Ltac clear_all :=
  match goal with
    | [id:_ |- _ ]    =>  clear id; clear_all
    | [ |- _ ]        =>  idtac
  end.

Theorem ring_example5 :
  forall n m:nat, n*0 + (n+1)*m = n*n*0 + m*n + m.
Proof.
  intros. ring.
Qed.

Theorem ring_example6 :
  forall n m:nat, n*0 + (S n)*m = n*n*0 + m*n + m.
Proof.
  intros. ring.  
Qed.


Theorem S_to_plus_one : forall n:nat, S n = n+1.
Proof.
  intros; rewrite plus_comm. reflexivity.
Qed.

Ltac S_to_plus_simpl :=
  match goal with
    | [ |- context [(S ?X1)] ]  =>
        match X1 with
          | 0%nat => fail 1 (* 1 refers to 'point of choice' : 0 -> | 0%nat , 1-> match X1 , 2 -> [ |- context ..]
          using '1' here prevents ?X2 to be attempted *)
          | ?X2   => rewrite (S_to_plus_one X2); S_to_plus_simpl
        end
    | [ |- _ ]                  =>  idtac
  end.

Ltac simpl_on e :=
  let v := eval simpl in e in
    match goal with
      | [ |- context [e] ] =>  replace e with v; [idtac | auto]
    end.

Theorem simpl_on_example:
  forall n:nat, exists m:nat, (1+n) + 4*(1+n) = 5*(S m).
Proof.
  intros n. simpl_on (1+n).
Abort. 




