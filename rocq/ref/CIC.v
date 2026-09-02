Require Import List.
Require Import Peano_dec.

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

(* xs represents the list of variables which are deemed 'bound'                 *)
Definition h_ (f:nat -> Exp) (xs:list nat) (x:nat) : Exp :=
    match in_dec eq_nat_dec x xs with
    | left  _   => EVar x                   (* x is deemed bound                *)
    | right _   => f x                      (* x is deemed free                 *) 
    end.

(* Unsure whether xs or (n :: xs) for 'T' in say 'forall (n:T), U'              *)
Fixpoint subst_ (f:nat -> Exp) (t:Exp) (xs:list nat) : Exp :=
    match t with
    | EProp         => EProp
    | ESet          => ESet
    | EType n       => EType n
    | EVar  n       => h_ f xs n
    | ECon  n       => ECon n
    | EProd n T U   => EProd n (subst_ f T xs) (subst_ f U (n :: xs))
    | ELam  n T U   => ELam  n (subst_ f T xs) (subst_ f U (n :: xs))
    | EApp t1 t2    => EApp (subst_ f t1 xs) (subst_ f t2 xs)
    | ELet n t T U  => ELet n (subst_ f t xs)(subst_ f T xs)(subst_ f U (n::xs))
    end.

(* Does not avoid variable capture so inappropriate in current form.            *)
Definition subst (f:nat -> Exp) (t:Exp) : Exp := subst_ f t [].


Definition replace (x:nat) (t:Exp) (u:nat) : Exp :=
    match eq_nat_dec u x with
    | left  _   => t        (* if u = x  return t   *)
    | right _   => EVar u   (* otherwise return u   *)
    end.

(* substituting term t in place of variable x in term s                         *)
Definition Sub (s t:Exp) (n:nat) : Exp := subst (replace n t) s.

(* Whether a term is a 'sort' or not. Needed to defined typing rules.           *)
Inductive isSort : Exp -> Prop :=
| SortProp : isSort EProp
| SortSet  : isSort ESet
| SortType : forall (n:nat), isSort (EType n)
.

(* Type for 'local declarations' of 'variables'                                 *)
Inductive LocalDecl : Type :=
| LAssume : nat -> Exp -> LocalDecl         (* n:T , T is a type                *)
| LDefine : nat -> Exp -> Exp -> LocalDecl  (* n := (t:T)                       *)
.

(* Variable involved must be distinct                                           *)
Definition LocalContext : Type := list LocalDecl. 

(* Whether a variable n is declared in the local context C.                     *)
Fixpoint inCtxVar (n:nat) (C:LocalContext) : Prop :=
    match C with
    | []        => False
    | d :: C'   =>
        match d with
        | LAssume m _   => (n = m) \/ inCtxVar n C'
        | LDefine m _ _ => (n = m) \/ inCtxVar n C'
        end
    end.

(* Whether a declaration is present in the local context C.                     *)
Fixpoint inCtxDecl (n:nat) (T:Exp) (C:LocalContext) : Prop :=
    match C with
    | []        => False
    | d :: C'   =>
        match d with
        | LAssume n' T'     => ((n = n') /\ (T = T')) \/ inCtxDecl n T C'
        | LDefine n' _ T'   => ((n = n') /\ (T = T')) \/ inCtxDecl n T C'
        end
    end.

(* Type for 'global declarations' of 'constants'                                *)
Inductive GlobalDecl : Type :=
| GAssume : nat -> Exp -> GlobalDecl        (* c:T, T is a type                 *)
| GDefine : nat -> Exp -> Exp -> GlobalDecl (* c := t : T                       *)
| GInduct : nat -> GlobalDecl               (* TBT, define inductive objects    *)
.
 
Definition GlobalEnv : Type := list GlobalDecl.

(* Whether a constant n is declared in the global environment E.                *)
Fixpoint inEnvConst (n:nat) (E:GlobalEnv) : Prop :=
    match E with
    | []        => False
    | d :: E'   =>
        match d with
        | GAssume m _   => (n = m) \/ inEnvConst n E'
        | GDefine m _ _ => (n = m) \/ inEnvConst n E'
        | GInduct m     => (n = m) \/ inEnvConst n E'
        end
    end.

(* Whether a declaration is present in the global environment E.                *)
Fixpoint inEnvDecl (n:nat) (T:Exp) (E:GlobalEnv) : Prop :=
    match E with
    | []        => False
    | d :: E'   =>
        match d with
        | GAssume n' T'     => ((n = n') /\ (T = T')) \/ inEnvDecl n T E'
        | GDefine n' _ T'   => ((n = n') /\ (T = T')) \/ inEnvDecl n T E'
        | GInduct _         => inEnvDecl n T E'
        end
    end.


(* Judgement: E[C] |- t:T                                                       *)
(* t is well-typed and has type T in the global env E and local context C       *)

(* Judgement: WF(E)[C]                                                          *)
(* The global env E is well-formed and the local context C is valid in E        *)

(* Definition: t is well-typed in E, iff there exists a local context C         *)
(* and a term T such that E[C] |- t:T can be derived from typing rules          *)

Inductive Entails : GlobalEnv -> LocalContext -> Exp -> Exp -> Prop :=
| AxProp: forall E C,
    WF E C                                  ->  (* WF(E)[C]                     *)
    Entails E C EProp (EType 1)                 (* E[C] |- Prop:Type(1)         *)
| AxSet: forall E C,
    WF E C                                  ->  (* WF(E)[C]                     *)
    Entails E C ESet (EType 1)                  (* E[C] |- Set:Type(1)          *)
| AxType: forall E C n,
    WF E C                                  ->  (* WF(E)[C]                     *)
    Entails E C (EType n) (EType (S n))         (* E[C] |- Type(n):Type(n+1)    *)
| Var: forall E C T n,
    WF E C                                  ->  (* WF(E)[C]                     *)
    inCtxDecl n T C                         ->  (* n:T or n := t:T (some t) in C*)
    Entails E C (EVar n) T                      (* E[C] |- n:T                  *)
| Con: forall E C T n,
    WF E C                                  ->  (* WF(E)[C]                     *)
    inEnvDecl n T E                         ->  (* n:T or n := t:T (some t) in E*)
    Entails E C (ECon n) T                      (* E[C] |- n:T                  *)
| ProdProp: forall E C T s n U,
    Entails E C T s                         ->  (* E[C] |- T:s                  *)
    isSort s                                ->  (* s is Prop, Set or Type(n)    *)
    Entails E ((LAssume n T) :: C) U EProp  ->  (* E[(n:T) :: C] |- U:Prop      *)
    Entails E C (EProd n T U) EProp             (* E[C] |- A(n:T),U  :Prop      *)
| ProdSet: forall E C T s n U,
    Entails E C T s                         ->  (* E[C] |- T:s                  *)
    (s = EProp \/ s = ESet)                 ->  (* s is Prop or Set             *)
    Entails E ((LAssume n T) :: C) U ESet   ->  (* E[(n:T) :: C] |- U:Set       *)
    Entails E C (EProd n T U) ESet              (* E[C] |- A(n:T),U  :Set       *)
| ProdType: forall E C T i n U,
    Entails E C T (EType i)                 ->  (* E[C] |- T:Type(i)            *)
    Entails E ((LAssume n T)::C) U (EType i)->  (* E[(n:T) :: C] |- U:Type(i)   *)
    Entails E C (EProd n T U) (EType i)         (* E[C] |- A(n:T),U  :Set       *)
| Lam: forall E C n T U s t,
    Entails E C (EProd n T U) s             ->
    Entails E ((LAssume n T)::C) t U        ->
    Entails E C (ELam n T t) (EProd n T U)
| App: forall E C t n U T u,
    Entails E C t (EProd n U T)             ->  (* E[C] |- t:A(n:U),T           *)
    Entails E C u U                         ->  (* E[C] |- u:U                  *)
    Entails E C (EApp t u) (Sub T u n)          (* E[C] |- (t u):T[u/n]         *)
| Let : forall E C t T n u U,
    Entails E C t T                         ->  (* E[C] |- t:T                  *)
    Entails E ((LDefine n t T)::C) u U      ->  (* E[(n := t:T)::C] |- u:U      *)
    Entails E C (ELet n t T u) (Sub U t n)      (* E[C] |- (let (n:=t:T) in u)  *)
                                                (*         : U[t/n]             *)
with WF : GlobalEnv -> LocalContext -> Prop :=  
| WEmpty: WF [] []
| WLocalAssume: forall E C T s n, 
    Entails E C T s                         ->  (* E[C] |- T:s                  *)
    isSort s                                ->  (* s is Prop, Set or Type(n)    *) 
    ~ inCtxVar n C                          ->  (* Var n not already in C       *)
    WF E ((LAssume n T) :: C)                   (* WF(E)[ (n:T) :: C]           *) 
| WLocalDef: forall E C t T n,
    Entails E C t T                         ->  (* E[C] |- t:T                  *)
    ~ inCtxVar n C                          ->  (* Var n not already in C       *)
    WF E ((LDefine n t T) :: C)                 (* WF(E)[ (n := t:T) :: C ]     *)
| WGlobalAssume: forall E T s n,         
    Entails E [] T s                        ->  (* E[[]] |- T:s                 *)
    isSort s                                ->  (* s is Prop, Set or Type(n)    *)
    ~ inEnvConst n E                        ->  (* Const n not already in E     *)
    WF ((GAssume n T) :: E) []                  (* WF((n:T) :: E)[]             *)
| WGlobalDef: forall E t T n,
    Entails E [] t T                        ->  (* E[[]] |- t:T                 *)
    ~ inEnvConst n E                        ->  (* Const n not already in E     *)
    WF ((GDefine n t T) :: E) []                (* WF((n := t:T) :: E)[]        *)                           
.

