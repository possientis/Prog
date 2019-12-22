Require Import List.
Import ListNotations.

(* Abstract syntax for 'calculus of inductive constructions'.                   *)
Inductive Exp : Type :=
| EProp : Exp                               (* sort 'Prop'                      *)
| ESet  : Exp                               (* sort 'Set'                       *)
| EType : nat -> Exp                        (* sort 'Type(n)'                   *) 
| EVar  : nat -> Exp                        (* variables                        *)
| ECon  : nat -> Exp                        (* constants                        *)
| EProd : nat -> Exp -> Exp -> Exp          (* forall (x:T), U                  *)
| ELam  : nat -> Exp -> Exp -> Exp          (* fun (x:T) => U                   *)
| EApp  : Exp -> Exp -> Exp                 (* application                      *)
| ELet  : nat -> Exp -> Exp -> Exp -> Exp   (* let x:=(t:T) in U                *)
.

(* Whether a term is a 'sort' or not. Needed to defined typing rules.           *)
Inductive isSort : Exp -> Prop :=
| SortProp : isSort EProp
| SortSet  : isSort ESet
| SortType : forall (n:nat), isSort (EType n)
.

(* Type for 'local declaration'                                                 *)
Inductive LocalDecl : Type :=
| LAssume : nat -> Exp -> LocalDecl         (* n:T , T is a type                *)
| LDefine : nat -> Exp -> Exp -> LocalDecl  (* n := (t:T)                       *)
.

(* Returns variable involved in given local declaration.                        *)
Definition declVar (decl:LocalDecl) : nat :=
    match decl with
    | LAssume n _   => n
    | LDefine n _ _ => n
    end.

(* Variable involved must be distinct                                           *)
Definition LocalContext : Type := list LocalDecl. 

Definition inLocCtx (n:nat) (C:LocalContext) : Prop := 
    In n (map declVar C).

Inductive GlobalDecl : Type :=
| GAssume : nat -> Exp -> GlobalDecl        (* c:T, T is a type                 *)
| GDefine : nat -> Exp -> Exp -> GlobalDecl (* c := t : T                       *)
| GInduct : nat -> GlobalDecl               (* TBT, define inductive objects    *)
.
 
(* Returns constant involved in given global declaration.                       *)
Definition declConst (decl:GlobalDecl) : nat :=
    match decl with
    | GAssume n _   => n
    | GDefine n _ _ => n
    | GInduct n     => n
    end.

Definition GlobalEnv : Type := list GlobalDecl.

Definition inGblEnv (n:nat) (E:GlobalEnv) : Prop := 
    In n (map declConst E).

(* Judgement: E[C] |- t:T                                                       *)
(* t is well-typed and has type T in the global env E and local context C       *)

(* Judgement: WF(E)[C]                                                          *)
(* The global env E is well-formed and the local context C is valid in E        *)

(* Definition: t is well-typed in E, iff there exists a local context C         *)
(* and a term T such that E[C] |- t:T can be derived from typing rules          *)

Inductive Entails : GlobalEnv -> LocalContext -> Exp -> Exp -> Prop :=
| AxProp: forall E C,
    WF E C                      ->          (* WF(E)[C]                         *)
    Entails E C EProp (EType 1)             (* E[C] |- Prop:Type(1)             *)
| AxSet: forall E C,
    WF E C                      ->          (* WF(E)[C]                         *)
    Entails E C ESet (EType 1)              (* E[C] |- Set:Type(1)              *)
| AxType: forall E C n,
    WF E C                      ->          (* WF(E)[C]                         *)
    Entails E C (EType n) (EType (S n))     (* E[C] |- Type(n):Type(n+1)        *)
with WF : GlobalEnv -> LocalContext -> Prop :=  
| WEmpty: WF [] []
| WLocalAssume: forall E C T s n, 
    Entails E C T s             ->          (* E[C] |- T:s                      *)
    isSort s                    ->          (* s is Prop, Set or Type(n)        *) 
    ~ inLocCtx n C              ->          (* Var n not already in C           *)
    WF E ((LAssume n T) :: C)               (* WF(E)[ (n:T) :: C]               *) 
| WLocalDef: forall E C t T n,
    Entails E C t T             ->          (* E[C] |- t:T                      *)
    ~ inLocCtx n C              ->          (* Var n not already in C           *)
    WF E ((LDefine n t T) :: C)             (* WF(E)[ (n := t:T) :: C ]         *)
| WGlobalAssume: forall E T s n,         
    Entails E [] T s            ->          (* E[[]] |- T:s                     *)
    isSort s                    ->          (* s is Prop, Set or Type(n)        *)
    ~ inGblEnv n E              ->          (* Const n not already in E         *)
    WF ((GAssume n T) :: E) []              (* WF((n:T) :: E)[]                 *)
| WGlobalDef: forall E t T n,
    Entails E [] t T            ->          (* E[[]] |- t:T                     *)
    ~ inGblEnv n E              ->          (* Const n not already in E         *)
    WF ((GDefine n t T) :: E) []            (* WF((n := t:T) :: E)[]            *)                           
.


