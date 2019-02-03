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

Arguments tbinopDenote {t1} {t2} {t} _ _ _.

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
    | t :: ts'  => prod (typeDenote t) (vstack ts')
    end.

Definition tinstrDenote (s1 s2:tstack) (i:tinstr s1 s2) 
    : vstack s1 -> vstack s2 :=
    match i with
    | TiNConst _ n        => fun s => (n,s)
    | TiBConst _ b        => fun s => (b,s)
    | @TiBinop _ _ _ _ b  => fun s =>
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

Fixpoint tconcat (t1 t2 t3:tstack) (p:tprog t1 t2) 
    : tprog t2 t3 -> tprog t1 t3 :=
    match p with
    | TNil _               => fun q => q
    | @TCons s1 s2 s3 i p' => fun q => TCons i (tconcat s2 s3 _ p' q)
    end.    

Arguments tconcat {t1} {t2} {t3} _ _.

Fixpoint tcompile (t:type) (e:texp t) (ts:tstack) : tprog ts (t :: ts) :=
    match e with
    | TNConst n             => TCons (TiNConst _ n) (TNil _)
    | TBConst b             => TCons (TiBConst _ b) (TNil _)
    | @TBinop _ _ _ b e1 e2 => tconcat (tcompile _ e2 _) 
        (tconcat (tcompile _ e1 _) (TCons (TiBinop _ b) (TNil _)))
    end. 

Arguments tcompile {t} _ _.


Lemma tconcat_correct: 
    forall (t1 t2 t3:tstack) (p:tprog t1 t2) (q:tprog t2 t3) (s:vstack t1),
    tprogDenote (tconcat p q) s = tprogDenote q (tprogDenote p s).
Proof.
    intros t1 t2 t3 p q. induction p as [t|s1 s2 s3 i r IH]; intros s; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
Qed.



Lemma tcompile_correct': forall (t:type) (e:texp t)(ts:tstack)(s:vstack ts),
    tprogDenote (tcompile e ts) s = (texpDenote e, s).
Proof.
    intros t e. induction e as [n|b|t1 t2 t3 b e1 H1 e2 H2]; intros ts s; simpl.
    - reflexivity.
    - reflexivity.
    - rewrite tconcat_correct. rewrite H2.
      rewrite tconcat_correct. rewrite H1.
      reflexivity.
Qed.

Theorem tcompile_correct: forall (t:type) (e:texp t),
    tprogDenote (tcompile e nil) tt = (texpDenote e, tt).
Proof.
    intros t e. apply tcompile_correct'.
Qed.


