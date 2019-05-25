Inductive exp : Set :=
| Nat  : nat  -> exp
| Bool : bool -> exp
| Plus : exp  -> exp -> exp
| And  : exp  -> exp -> exp
.

Inductive type : Set := 
| TNat  : type  
| TBool : type
.

Inductive hasType : exp -> type -> Prop :=
| HtNat  : forall (n:nat),  hasType (Nat n) TNat
| HtBool : forall (b:bool), hasType (Bool b) TBool
| HtPlus : forall (e1 e2:exp), 
    hasType e1 TNat -> 
    hasType e2 TNat -> 
    hasType (Plus e1 e2) TNat 
| HtAnd  : forall (e1 e2:exp),
    hasType e1 TBool -> 
    hasType e2 TBool -> 
    hasType (And e1 e2) TBool
.

(* The lazy way                                                                 *)
Definition eq_type_dec : forall (t t':type), {t = t'} + {t <> t'}.
    decide equality.
Defined.

(*
Print eq_type_dec.
*)

(* The usual way                                                                *)
Definition eq_type_dec' : forall (t t':type), {t = t'} + {t <> t'}.
    intros t t'. destruct t, t'.
    - left. reflexivity.
    - right. intros H. inversion H.
    - right. intros H. inversion H.
    - left. reflexivity.
Defined.

(*
Print eq_type_dec'.
*)

Definition nat_not_bool : TNat <> TBool := fun p =>
    match p with end.

Definition bool_not_nat : TBool <> TNat := fun p =>
    match p with end.

(* The hand-crafted way                                                         *)
Definition eq_type_dec'' (t t':type) : {t = t'} + {t <> t'} :=
    match t as s return {s = t'} + {s <> t'} with
    | TNat  =>
        match t' as s' return {TNat = s'} + {TNat <> s'} with
        | TNat  => left eq_refl
        | TBool => right nat_not_bool
        end
    | TBool =>
        match t' as s' return {TBool = s'} + {TBool <> s'} with
        | TNat  => right bool_not_nat
        | TBool => left eq_refl
        end
    end.

(*
Print eq_type_dec''.
*)

(* Hoping to turn 'Typ' into a monad - ish                                      *)
Definition Typ (e:exp) : Type := option {t:type | hasType e t}.

Definition return_ (e:exp) (t:type) (p:hasType e t) : Typ e := 
    Some (exist _ t p).



(* define monadic structure of returned type and relevant do notation
Definition typeCheck (e:exp) : option {t:type |hasType e t}.

Show.
*)
