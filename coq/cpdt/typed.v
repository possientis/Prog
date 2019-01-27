Require Import Arith.
Require Import Bool.
Require Import List.

Fixpoint blt_nat (n m:nat) : bool :=
    match n with
    | 0 => 
        match m with
        | 0     => false
        | S _   => true
        end
    | S n'  =>
        match m with
        | 0     => false
        | S m'  => blt_nat n' m'
        end
    end.

Lemma blt_nat_test1 : blt_nat 0 0 = false.
Proof. reflexivity. Qed.

Lemma blt_nat_test2 : blt_nat 1 0 = false.
Proof. reflexivity. Qed.

Lemma blt_nat_test3 : blt_nat 0 1 = true.
Proof. reflexivity. Qed.

Lemma blt_nat_test4 : blt_nat 1 1 = false.
Proof. reflexivity. Qed.

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

Lemma typeDenote_test1 : typeDenote Nat = nat.
Proof. reflexivity. Qed.

Lemma typeDenote_test2 : typeDenote Bool = bool.
Proof. reflexivity. Qed.

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

Lemma tbinopDenote_test1 : tbinopDenote TPlus = plus.
Proof. reflexivity. Qed.

Lemma tbinopDenote_test2 : tbinopDenote TTimes = mult.
Proof. reflexivity. Qed.

Lemma tbinopDenote_test3 : tbinopDenote (TEq Nat) = beq_nat.
Proof. reflexivity. Qed.

Lemma tbinopDenote_test4 : tbinopDenote (TEq Bool) = eqb.
Proof. reflexivity. Qed.

Lemma tbinopDenote_test5 : tbinopDenote TLt = blt_nat.
Proof. reflexivity. Qed.

Fixpoint texpDenote (t:type) (e:texp t) : typeDenote t :=
    match e with
    | TNConst n               => n
    | TBConst b               => b
    | @TBinop t1 t2 _ b e1 e2 => tbinopDenote b (texpDenote t1 e1) (texpDenote t2 e2)
    end.
    
Arguments texpDenote {t} _.

Lemma texpDenote_test1 : texpDenote (TNConst 42) = 42.
Proof. reflexivity. Qed.

Lemma texpDenote_test2 : texpDenote (TBConst true) = true.
Proof. reflexivity. Qed.

Lemma texpDenote_test3 : texpDenote (TBConst false) = false.
Proof. reflexivity. Qed.

Lemma texpDenote_test4 : texpDenote 
    ( TBinop TTimes 
        (TBinop TPlus (TNConst 2)(TNConst 3)) 
        (TNConst 7)) = 35.
Proof. reflexivity. Qed.

Lemma texpDenote_test5 : texpDenote 
    ( TBinop (TEq Nat) 
        (TBinop TPlus (TNConst 4) (TNConst 3))
        (TNConst 7)) = true.
Proof. reflexivity. Qed.

Lemma texpDenote_test6 : texpDenote 
    ( TBinop (TEq Bool) 
        (TBinop (TEq Nat) (TNConst 2) (TNConst 3))
        (TBConst false)) = true.
Proof. reflexivity. Qed.

Lemma texpDenote_test7 : texpDenote 
    ( TBinop TLt
        (TBinop TPlus (TNConst 2) (TNConst 3))
        (TNConst 7)) = true.
Proof. reflexivity. Qed.

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

Definition x : unit := tt.

Definition tinstrDenote (s1 s2:tstack) (i:tinstr s1 s2) : vstack s1 -> vstack s2 :=
    match i with
    | TiNConst _ n => fun s => (n,s)
    | TiBConst _ b => fun s => (b,s)
    | TiBinop _ b  => fun s =>
        let '(v1, (v2, s')) := s in 
            ((tbinopDenote b) v1 v2, s')
    end.

Arguments tinstrDenote {s1} {s2} _ _.

Fixpoint tprogDenote (s1 s2:tstack) (p:tprog s1 s2) : vstack s1 -> vstack s2 :=
    match p with 
    | TNil _               => fun s => s
    | @TCons s1 s2 s3 i p' => fun s => tprogDenote s2 s3 p' (tinstrDenote i s)  
    end. 

Arguments tprogDenote {s1} {s2} _ _.
