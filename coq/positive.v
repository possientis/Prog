Set Implicit Arguments.
Require Import ZArith.

Print positive.
(*
Inductive positive : Set :=
xI : positive -> positive | xO : positive -> positive | xH : positive
*)

Print Z.
(*
Inductive Z : Set :=  Z0 : Z | Zpos : positive -> Z | Zneg : positive -> Z
*)

Check positive_ind.
(*
forall P : positive -> Prop,
  (forall p : positive, P p -> P (p~1)%positive) ->
  (forall p : positive, P p -> P (p~0)%positive) ->
   P 1%positive -> forall p : positive, P p
*)

Fixpoint Psucc (x:positive) : positive :=
  match x with
    | xI x' => xO (Psucc x') 
    | xO x' => xI x'
    | xH    => 2%positive
  end.

Eval compute in Psucc (234%positive).
Eval compute in Psucc (63%positive).

(*
Open Scope positive_scope.
*)

Eval compute in xO (xO (xO (xI (xO (xI (xI (xI (xI xH)))))))).
Eval compute in (1~1~1~1~1~0~1~0~0~0)%positive. (* 1000 *)
Eval compute in (1~1~0~0~1)%positive.           (* 25 *)
Eval compute in (1~0~0~0~0~0~0~0~0~0)%positive. (* 512 *)

Definition pos_even_bool (n:positive) : bool :=
  match n with
    | xO p      => true
    | xI p      => false
    | xH        => false
  end.

Eval compute in pos_even_bool 1%positive.
Eval compute in pos_even_bool 2.
Eval compute in pos_even_bool 3%positive.

Definition pos_to_int (n:positive): Z := Zpos n.

Definition pos_div2 (n:positive) : Z :=
  match n with
    | xO p      => Zpos p
    | xI p      => Zpos p
    | xH        => Z0
  end.

Eval compute in pos_div2 127%positive.

Definition pos_div4 (n:positive) : Z :=
  match n with 
    | xO (xO p) => Zpos p
    | xI (xO p) => Zpos p
    | xO (xI p) => Zpos p
    | xI (xI p) => Zpos p
    | other     => Z0
  end.

Eval compute in pos_div4 1%positive.
Eval compute in pos_div4 2%positive.
Eval compute in pos_div4 3%positive.
Eval compute in pos_div4 4%positive.
Eval compute in pos_div4 5%positive.
Eval compute in pos_div4 6%positive.
Eval compute in pos_div4 7%positive.
Eval compute in pos_div4 8%positive.

Variable pos_mult : positive -> positive -> positive.

Definition new_Z_mult (n m : Z) : Z :=
  match (n, m) with 
    | (Z0, _ )          => 0%Z
    | (_ , Z0)          => 0%Z
    | (Zpos x, Zpos y)  => Zpos (pos_mult x y)
    | (Zpos x, Zneg y)  => Zneg (pos_mult x y)
    | (Zneg x, Zpos y)  => Zneg (pos_mult x y)
    | (Zneg x, Zneg y)  => Zpos (pos_mult x y)
  end.

Inductive prop : Set :=
  | And : prop -> prop -> prop
  | Or  : prop -> prop -> prop
  | Not : prop -> prop
  | Imp : prop -> prop -> prop
  | Top : prop
  | Bot : prop.

(* any positive rational can be obtained by a unique sequence
of application of N and D below, starting from 1 *)

Inductive pos_ratio : Set :=
  | One : pos_ratio
  | N   : pos_ratio -> pos_ratio  (* x -> 1 + x *)
  | D   : pos_ratio -> pos_ratio. (* x -> 1 + 1/x *)


Fixpoint power (z:Z)(n:nat) : Z :=
  match n with
    | 0         => 1%Z
    | S p       => (z * power z p)%Z
  end.

Eval compute in power 2 20.

Fixpoint discrete_log (p: positive) : nat :=
  match p with
    | xH        =>  0
    | xO p'     => S (discrete_log p')
    | xI p'     => S (discrete_log p')
  end.

Eval compute in discrete_log 1024.
Eval compute in discrete_log 2048.







