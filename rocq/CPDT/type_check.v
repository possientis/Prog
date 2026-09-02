Require Import option.

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

(* This signature looks very good in that it seems to guarantee correctness     *)
(* since if it returns a type t, this type will be accompanied by a proof of    *)
(* hasType e t. Unfortunately, this is only half of a correctness proof:        *)
(* We have to guarantee that if hasType e t holds, typeCheck is not None        *)
(* Proving correctness and reasoning about typeCheck appears to be difficult    *)
(* It would be better to design a new signature which ensures correctness       *)
Definition typeCheck : forall (e:exp), option {t:type | hasType e t}.
    refine (fix F (e:exp) : option {t:type | hasType e t} :=
        match e as e' return option {t:type | hasType e' t} with
        | Nat _      => Some (exist _ TNat (HtNat _))
        | Bool _     => Some (exist _ TBool (HtBool _))
        | Plus e1 e2 => 
            match (F e1) with 
            | None  => None
            | Some (exist _ t1 p1) => 
                match (F e2) with
                | None  => None
                | Some (exist _ t2 p2) =>
                    match eq_type_dec t1 TNat with
                    | right _  => None
                    | left  _  =>
                        match eq_type_dec t2 TNat with
                        | right _  => None
                        | left _   => Some (exist _ TNat (HtPlus _ _ _ _))
                        end 
                    end

                end
            end
        | And e1 e2  => 
            match (F e1) with 
            | None  => None
            | Some (exist _ t1 p1)  =>
                match (F e2) with
                | None  => None
                | Some (exist _ t2 p2)  =>
                    match eq_type_dec t1 TBool with
                    | right _  => None
                    | left _   =>
                        match eq_type_dec t2 TBool with
                        | right _  => None
                        | left _   => Some (exist _ TBool (HtAnd _ _ _ _))
                        end
                    end
                end
            end
        end).
    - simpl in p1. subst. assumption.
    - simpl in p2. subst. assumption. 
    - simpl in p1. subst. assumption.
    - simpl in p2. subst. assumption.
Defined.

(*
Print typeCheck.
*)

Definition isNat (e:exp)(t' : {t:type | hasType e t}) : bool :=
    match t' with
    | exist _ t _   =>
        match eq_type_dec t TNat with
        | right _   => false
        | left  _   => true
        end
    end.

Arguments isNat {e} _.


Lemma isNatHasTypeNat : forall (e:exp) (t' : {t:type | hasType e t}),
    isNat t' = true -> hasType e TNat.
Proof.
    intros e [t p]. simpl. destruct (eq_type_dec t) as [H|H].
    - rewrite H in p. intros. assumption.
    - intros H'. inversion H'.
Qed.

Definition isBool (e:exp)(t' : {t:type | hasType e t}) : bool :=
    match t' with
    | exist _ t _   =>
        match eq_type_dec t TBool with
        | right _   => false
        | left  _   => true
        end
    end.

Arguments isBool {e} _.

Lemma isBoolHasTypeBool : forall (e:exp) (t' : {t:type | hasType e t}),
    isBool t' = true -> hasType e TBool.
Proof.
    intros e [t p]. simpl. destruct (eq_type_dec t) as [H|H].
    - rewrite H in p. intros. assumption.
    - intros H'. inversion H'.
Qed.

(* This is a lot more readable than the initial typeCheck implementation        *)
Definition typeCheck' : forall (e:exp), option {t:type | hasType e t}.
    refine (fix F (e:exp) : option {t:type | hasType e t} :=
        match e as e' return option {t:type | hasType e' t} with
        | Nat _      => Some (exist _ TNat (HtNat _))
        | Bool _     => Some (exist _ TBool (HtBool _))
        | Plus e1 e2 => 
            t1 <- F e1 ;
            t2 <- F e2 ;
            p1  <- guard (isNat t1) ; 
            p2  <- guard (isNat t2) ;
            Some (exist _ TNat (HtPlus _ _ _ _))
        | And e1 e2  =>
            t1 <- F e1 ;
            t2 <- F e2 ;
            p1 <- guard (isBool t1) ;
            p2 <- guard (isBool t2) ;
            Some (exist _ TBool (HtAnd _ _ _ _))
        end). 
    - apply isNatHasTypeNat   with t1. assumption.
    - apply isNatHasTypeNat   with t2. assumption.
    - apply isBoolHasTypeBool with t1. assumption.
    - apply isBoolHasTypeBool with t2. assumption.
Defined. (* not 'Qed' which would make function opaque                          *)

(* Throws away the proof element                                                *)
Definition typeOf (e:exp) (t':{t:type | hasType e t}) : type :=
    match t' with
    | exist _ t _  => t
    end.

Arguments typeOf {e} _.

(*
Compute typeOf <$> (typeCheck (Nat 5)).
Compute typeOf <$> (typeCheck (Bool true)).
Compute typeOf <$> (typeCheck (Plus (Nat 5) (Plus (Nat 6) (Nat 0)))).
Compute typeOf <$> (typeCheck (And (Bool true) (Bool false))).
Compute typeOf <$> (typeCheck (Plus (Bool true) (Nat 5))).
Compute typeOf <$> (typeCheck' (Nat 5)).
Compute typeOf <$> (typeCheck' (Bool true)).
Compute typeOf <$> (typeCheck' (Plus (Nat 5) (Plus (Nat 6) (Nat 0)))).
Compute typeOf <$> (typeCheck' (And (Bool true) (Bool false))).
Compute typeOf <$> (typeCheck' (Plus (Bool true) (Nat 5))).
*)

Lemma hasType_unique : forall (e:exp) (t t':type),
    hasType e t -> hasType e t' -> t = t'.
Proof.
    destruct e as [n|b|e1 e2|e1i e2]; 
    intros t t' H H'; 
    inversion H; inversion H'; 
    reflexivity.
Qed.

(* This correctness result is pretty much guaranteed by the type system         *)
Lemma typeCheck_correct1 : forall (e:exp) (t:type),
    typeOf <$> typeCheck e = Some t -> hasType e t.
Proof.
    intros e t H. destruct (typeCheck e) as [[t' H']|];
    simpl in H; inversion H. subst. assumption.
Qed.

(* Identical proof, all coming from the type signature of typeCheck             *)
Lemma typeCheck_correct1' : forall (e:exp) (t:type),
    typeOf <$> typeCheck' e = Some t -> hasType e t.
Proof.
    intros e t H. destruct (typeCheck' e) as [[t' H']|];
    simpl in H; inversion H. subst. assumption.
Qed.

(*
Lemma typeCheck_correct2 : forall (e:exp) (t:type),
    hasType e t -> typeOf <$> typeCheck e = Some t.
Proof.
    intros e t H. induction H as [n|b|e1 e2 H1 IH1 H2 IH2|e1 e2 H1 IH1 H2 IH2].
    - reflexivity.
    - reflexivity.
    - simpl. destruct (typeCheck e1) as [|t1 p1] eqn:E1, (typeCheck e2) as [|t2 p2] eqn:E2.
        + simpl in IH1. inversion IH1. subst.

Show.
*)



(*
(* It is all very nice to define typeCheck with 'do' notations, but correct?    *)
Lemma typeCheck_correct : forall (e:exp),
    typeOf <$> typeCheck e = typeOf <$> typeCheck' e.
Proof.    
    induction e as [n|b|e1 IH1 e2 IH2|e1 IH1 e2 IH2].
    - simpl. reflexivity.
    - simpl. reflexivity.
    -    
Show.
*)
