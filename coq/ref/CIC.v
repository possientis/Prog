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
| LAssume : nat -> Exp -> LocalDecl         (* x:T , T is a type                *)
| LDefine : nat -> Exp -> Exp -> LocalDecl  (* x := (t:T)                       *)
.

Definition declVar (decl:LocalDecl) : nat :=
    match decl with
    | LAssume n _   => n
    | LDefine n _ _ => n
    end.

(* variable involved must be distinct                                           *)
Definition LocalContext : Type := list LocalDecl. 

Definition inLocCtx (n:nat) (ctx:LocalContext) : Prop := 
    In n (map declVar ctx).

Inductive GlobalDecl : Type :=
| GAssume : nat -> Exp -> GlobalDecl        (* c:T, T is a type                 *)
| GDefine : nat -> Exp -> Exp -> GlobalDecl (* c := t : T                       *)
| GInduct : GlobalDecl                      (* TBT, define inductive objects    *)
.

Definition GlobalEnv : Type := list GlobalDecl.

(* Judgement: E[C] |- t:T                                                       *)
(* t is well-typed and has type T in the global env E and local context C       *)

(* Judgement: WF(E)[C]                                                          *)
(* The global env E is well-formed and the local context C is valid in E        *)

(* Definition: t is well-typed in E, iff there exists a local context C         *)
(* and a term T such that E[C] |- t:T can be derived from typing rules          *)

Inductive Entails : GlobalEnv -> LocalContext -> Exp -> Exp -> Prop :=


with WF : GlobalEnv -> LocalContext -> Prop :=  
| WEmpty: WF [] []
| WLocalAssume: forall env ctx T s n, 
    Entails env ctx T s -> 
    isSort s            -> 
    ~ inLocCtx n ctx    -> 
    WF env ((LAssume n T) :: ctx) 
| WLocalDef: forall env ctx t T n,
    Entails env ctx t T ->
    ~ inLocCtx n ctx    ->
    WF env ((LDefine n t T) :: ctx)
.


