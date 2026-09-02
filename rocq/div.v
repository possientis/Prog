Require Import ZArith.

Open Scope Z_scope.

Fixpoint div_bin (n m:positive) : Z*Z :=
  match n with
    | 1%positive    =>  match m with
                          | 1%positive    => (1,0)
                          | v             => (0,1)
                        end
    | xO n'         =>  let (q',r') := div_bin n' m in
                        match Z_lt_ge_dec (2*r')(Zpos m) with
                          | left _    => (2*q', 2*r')
                          | right _   => (2*q'+1, 2*r' - (Zpos m))
                        end
    | xI n'         =>  let (q',r') := div_bin n' m in 
                        match Z_lt_ge_dec (2*r'+1)(Zpos m) with
                          | left _    => (2*q', 2*r' + 1)
                          | right _   => (2*q' + 1, (2*r'+1)-(Zpos m))
                        end
  end.


Lemma rem_1_1_interval : 0 <= 0 < 1.
Proof.
  auto with zarith. (* omega also works *)
Qed.


Lemma rem_1_even_interval : forall m: positive, 
  0 <= 1 < Zpos (xO m).
Proof.
  intros m. split. 
  auto with zarith.
(*
Nothing comes up
SearchPattern (1 < Zpos _).
*)
(*
Locate "_ < _".
  Notation            Scope     
  "x < y" := Pos.lt x y          : positive_scope
                        
  "x < y" := lt x y    : nat_scope
                        
  "x < y" := Z.lt x y  : Z_scope (default interpretation)
  "x < y" := N.lt x y  : N_scope
*)
(*
Print Z.lt.
Z.lt = fun x y : Z => (x ?= y) = Lt
     : Z -> Z -> Prop
*)
compute. (* trick !!!! simpl fails but compute works !!! *)
reflexivity.
Qed.

Lemma rem_1_odd_interval : forall m:positive,
  0 <= 1 < Zpos(xI m).
Proof.
  intros m. split.
  auto with zarith.
  compute. reflexivity.
Qed.

Lemma rem_even_ge_interval : forall m r:Z,
  0 <= r < m -> m <= 2*r -> 0 <= 2*r - m < m.
Proof.
  intros. omega.
Qed.

Lemma rem_even_lt_interval: forall m r:Z,
  0 <= r < m -> 2*r < m -> 0 <= 2*r < m.
Proof.
  intros. omega.
Qed.


Lemma rem_odd_ge_interval: forall m r:Z,
  0 <= r < m -> m <= 2*r + 1 -> 0 <= 2*r + 1 - m < m.
Proof.
  intros. omega.
Qed.

Lemma rem_odd_lt_interval: forall m r:Z,
  0 <= r < m -> 2*r + 1 < m -> 0 <= 2*r + 1 < m.
Proof.
  intros. omega.
Qed.

Ltac div_bin_tac arg1 arg2 :=
  elim arg1;
    [intros p; lazy beta iota delta [div_bin]; fold div_bin;
      case (div_bin p arg2); unfold snd; intros q' r' Hrec;
      case (Z_lt_ge_dec (2*r' + 1)(Zpos arg2)); intros H
    | intros p; lazy beta iota delta [div_bin]; fold div_bin;
      case (div_bin p arg2); unfold snd; intros q' r' Hrec;
      case (Z_lt_ge_dec (2*r')(Zpos arg2)); intros H
    | case arg2; lazy beta iota delta [div_bin]; intros].

Hint Resolve rem_odd_ge_interval rem_even_ge_interval
rem_odd_lt_interval rem_even_lt_interval rem_1_odd_interval
rem_1_even_interval rem_1_1_interval.

Theorem div_bin_rem_lt:
  forall n m:positive, 0 <= snd (div_bin n m) < Zpos m.
Proof.
  intros n m. div_bin_tac n m; unfold snd; auto; omega.
Qed.

(* fails...
SearchRewrite (Zpos (xI _)).
*)

(*
Check Zpos_xI.
  Pos2Z.inj_xI
       : forall p : positive, Z.pos p~1 = 2 * Z.pos p + 1
*)

(*
Check Zpos_xO.
  Pos2Z.inj_xO
       : forall p : positive, Z.pos p~0 = 2 * Z.pos p
*)

Theorem div_bin_eq:
  forall n m:positive, Zpos n = (fst (div_bin n m))*(Zpos m) + snd (div_bin n m).
Proof.
  intros n m. div_bin_tac n m;
  rewrite Zpos_xI || (try rewrite Zpos_xO);
  try rewrite Hrec; unfold fst, snd; ring.
Qed.

Inductive div_data (n m:positive) : Set :=
  | div_data_def : forall q r:Z, 
    Zpos n = q*(Zpos m)+r -> 0 <= r < Zpos m -> div_data n m.


Definition div_bin2 : forall n m:positive, div_data n m.
  intros n m. elim n.
  intros n' [q r H_eq H_int].
  case (Z_lt_ge_dec (2*r + 1)(Zpos m)).
  exists (2*q)(2*r + 1).
  rewrite Zpos_xI; rewrite H_eq; ring.
  auto.
  exists (2*q+1)(2*r + 1 - (Zpos m)).
  rewrite Zpos_xI; rewrite H_eq; ring.
  omega.
Abort.

Definition div_bin3 : forall n m:positive, div_data n m.
  refine
    ((fix div_bin3 (n:positive) : forall m:positive, div_data n m :=
      fun m =>
        match n return div_data n m with
          | 1%positive  =>
            match m return div_data 1 m with
              | 1%positive => div_data_def 1 1 1 0 _ _
              | xO p => div_data_def 1 (xO p) 0 1 _ _
              | xI p => div_data_def 1 (xI p) 0 1 _ _
            end
          | xO p  =>
            match div_bin3 p m with
              | div_data_def q r H_eq H_int =>
                  match Z_lt_ge_dec (Zmult 2 r)(Zpos m) with
                    | left hlt =>
                        div_data_def (xO p) m (Zmult 2 q)
                                     (Zmult 2 r) _ _
                    | right hge =>
                        div_data_def (xO p) m (Zplus (Zmult 2 q) 1)
                                     (Zminus (Zmult 2 r)(Zpos m)) _ _
                  end
            end
          | xI p =>
            match div_bin3 p m with
              | div_data_def q r H_eq H_int =>
                  match Z_lt_ge_dec (Zplus (Zmult 2 r) 1)(Zpos m) with
                    | left hlt =>
                        div_data_def (xI p) m (Zmult 2 q)
                                     (Zplus (Zmult 2 r) 1) _ _
                    | right hge =>
                        div_data_def (xI p) m (Zplus (Zmult 2 q) 1)
                        (Zminus (Zplus (Zmult 2 r) 1)(Zpos m)) _ _
                  end
              end
            end));
  clear div_bin3; try rewrite Zpos_xI; try rewrite Zpos_xO;
  try rewrite H_eq; auto with zarith; try (ring; fail).
  split;[auto with zarith | compute; auto].
  split;[auto with zarith | compute; auto].
Defined.






