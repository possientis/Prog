Require Import Arith.

Definition Var := nat.

Definition Env := Var -> nat.

Definition empty : Env := fun v => 0.

Definition update (env:Env) (v:Var) (n:nat) : Env :=
    fun (x:Var) => if beq_nat x v then n else env x.

Inductive Exp : Set :=
| EConst : nat -> Exp
| EVar   : Var -> Exp
| EPlus  : Exp -> Exp -> Exp
.

(* interpreter fixes the semantics *)
Fixpoint evalExp (env:Env) (e:Exp) : nat :=
    match e with
    | EConst n      => n
    | EVar v        => env v
    | EPlus e1 e2   => evalExp env e1 + evalExp env e2
    end.

Example test_evalExp1 : evalExp empty (EConst 5) = 5.
Proof. reflexivity. Qed.

Example test_evalExp2 : evalExp (update empty 3 12) (EVar 3) = 12.
Proof. reflexivity. Qed.

Example test_evalExp3 : evalExp (update empty 3 12)(EPlus(EConst 5)(EVar 3)) = 17.
Proof. reflexivity. Qed.


Inductive Cmd : Set :=
| CAssign : Var -> Exp -> Cmd
| CSeq    : Cmd -> Cmd -> Cmd
| CWhile  : Exp -> Cmd -> Cmd
.


CoInductive evalCmd : Env -> Cmd -> Env -> Prop :=
| EvalAssign : forall (env:Env) (v:Var) (e:Exp), 
    evalCmd env (CAssign v e) (update env v (evalExp env e))
| EvalSeq : forall (e1 e2 e3:Env) (c1 c2:Cmd),
    evalCmd e1 c1 e2 -> evalCmd e2 c2 e3 -> evalCmd e1 (CSeq c1 c2) e3
| EvalWhileFalse : forall (env:Env) (e:Exp) (c:Cmd),
    evalExp env e = 0 -> evalCmd env (CWhile e c) env
| EvalWhileTrue : forall (e1 e2 e3:Env) (e:Exp) (c:Cmd),
    evalExp e1 e <> 0 -> evalCmd e1 c e2 -> evalCmd e2 (CWhile e c) e3 -> 
        evalCmd e1 (CWhile e c) e3
.

(* Need to build a coinduction principle for evalCmd *)
Theorem evalCmd_coind : forall (R:Env -> Cmd -> Env -> Prop),
    (forall (e1 e2:Env) (e:Exp) (v:Var), 
        R e1 (CAssign v e) e2 -> e2 = update e1 v (evalExp e1 e))    ->
    (forall (e1 e2 e3:Env) (c1 c2:Cmd),
        R e1 (CSeq c1 c2) e3 -> exists e2, R e1 c1 e2 /\ R e2 c2 e3) -> 
    (forall (e1 e2 e3:Env) (e:Exp) (c:Cmd),
        R e1 (CWhile e c) e3 -> (evalExp e1 e = 0 /\ e3 = e1) \/ 
        (exists (e2:Env), 
            evalExp e1 e <> 0 /\ R e1 c e2 /\ R e2 (CWhile e c) e3)) ->
    (forall (e1 e2:Env) (c:Cmd), R e1 c e2 -> evalCmd e1 c e2).
Proof.

Show.
