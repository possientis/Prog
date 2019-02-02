Require Import Arith.
Require Import Bool.
Require Import List.

Require Import Utils.nat.

Inductive type : Set := Nat | Bool.

Inductive tbinop : type -> type -> type -> Set :=
| TPlus  : tbinop Nat Nat Nat
| TTimes : tbinop Nat Nat Nat
| TEq    : forall (t:type), tbinop t t Bool
| TLt    : tbinop Nat Nat Bool
.

Inductive texp : type -> Set :=
| TNConst : nat  -> texp Nat
| TBConst : bool -> texp Bool
| TBinop  : forall (t1 t2 t:type), tbinop t1 t2 t -> texp t1 -> texp t2 -> texp t
.

Arguments TBinop {t1} {t2} {t} _ _ _.
    
Definition typeDenote (t:type) : Set :=
    match t with
    | Nat   => nat
    | Bool  => bool
    end.

Definition tbinopDenote (t1 t2 t:type) (b:tbinop t1 t2 t) 
    : typeDenote t1 -> typeDenote t2 -> typeDenote t := 
        match b with 
        | TPlus    => plus
        | TTimes   => mult
        | TEq Nat  => beq_nat
        | TEq Bool => eqb 
        | TLt      => blt_nat
        end.

Arguments tbinopDenote {t1} {t2} {t} _.

Fixpoint texpDenote (t:type) (e:texp t) : typeDenote t :=
    match e with
    | TNConst n               => n
    | TBConst b               => b
    | @TBinop t1 t2 _ b e1 e2 => 
            tbinopDenote b (texpDenote t1 e1) (texpDenote t2 e2)
    end.
    
Arguments texpDenote {t} _.

Definition tstack := list type.

Inductive tinstr : tstack -> tstack -> Set :=
| TiNConst : forall (s:tstack) (n:nat) , tinstr s (Nat :: s)
| TiBConst : forall (s:tstack) (b:bool), tinstr s (Bool :: s)
| TiBinop  : forall (t1 t2 t:type) (s:tstack), 
    tbinop t1 t2 t -> tinstr (t1 :: t2 :: s) (t :: s) 
.

Arguments TiBinop {t1} {t2} {t} _ _. 

Inductive tprog : tstack -> tstack -> Set :=
| TNil  : forall (s:tstack), tprog s s
| TCons : forall (s1 s2 s3:tstack), tinstr s1 s2 -> tprog s2 s3 -> tprog s1 s3
.

Arguments TCons {s1} {s2} {s3} _ _.

Fixpoint vstack (ts:tstack) : Set :=
    match ts with 
    | nil       => unit
    | t :: ts'  => typeDenote t * vstack ts'
    end.

Definition tinstrDenote (s1 s2:tstack) (i:tinstr s1 s2) 
    : vstack s1 -> vstack s2 :=
    match i with
    | TiNConst _ n => fun s => (n,s)
    | TiBConst _ b => fun s => (b,s)
    | TiBinop _ b  => fun s =>
        let '(v1, (v2, s')) := s in 
            ((tbinopDenote b) v1 v2, s')
    end.

Arguments tinstrDenote {s1} {s2} _ _.

Fixpoint tprogDenote (s1 s2:tstack) (p:tprog s1 s2) 
    : vstack s1 -> vstack s2 :=
    match p with 
    | TNil _               => fun s => s
    | @TCons s1 s2 s3 i p' => fun s => tprogDenote s2 s3 p' (tinstrDenote i s)  
    end. 

Arguments tprogDenote {s1} {s2} _ _.
