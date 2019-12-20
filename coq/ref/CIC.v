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

Inductive LocalDecl : Type :=
| LAssume : nat -> Exp -> LocalDecl         (* x:T , T is a type                *)
| LDefine : nat -> Exp -> Exp -> LocalDecl  (* x := (t:T)                       *)
.

(* variable involved must be distinct                                           *)
Definition LocalContext : Type := list LocalDecl. 

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


