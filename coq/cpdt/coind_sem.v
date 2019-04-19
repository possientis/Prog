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

(* Need to build a coinduction principle for evalCmd        *)
Theorem evalCmd_coind : forall (R:Env -> Cmd -> Env -> Prop),
    (forall (e1 e2:Env) (e:Exp) (v:Var), 
        R e1 (CAssign v e) e2 -> e2 = update e1 v (evalExp e1 e))    ->
    (forall (e1 e3:Env) (c1 c2:Cmd),
        R e1 (CSeq c1 c2) e3 -> exists e2, R e1 c1 e2 /\ R e2 c2 e3) -> 
    (forall (e1 e3:Env) (e:Exp) (c:Cmd),
        R e1 (CWhile e c) e3 -> (evalExp e1 e = 0 /\ e3 = e1) \/ 
        (exists (e2:Env), 
            evalExp e1 e <> 0 /\ R e1 c e2 /\ R e2 (CWhile e c) e3)) ->
    (forall (e1 e2:Env) (c:Cmd), R e1 c e2 -> evalCmd e1 c e2).
Proof.
    intros R H1 H2 H3. cofix. intros e1 e2 c H. destruct c.
    - apply H1 in H. rewrite H. constructor.
    - rename e2 into e3. apply H2 in H. destruct H as [e2 [H12 H23]].
      apply EvalSeq with e2; apply evalCmd_coind; assumption.
    - rename e2 into e3. apply H3 in H. destruct H as [H|H].
        + destruct H as [E1 E2]. subst. apply EvalWhileFalse. assumption.
        + destruct H as [e2 [E1 [E2 E3]]]. apply EvalWhileTrue with e2.
            { assumption. }
            { apply evalCmd_coind. assumption. }
            { apply evalCmd_coind. assumption. }
Qed.

Fixpoint optExp (e:Exp) : Exp :=
    match e with
    | EPlus (EConst 0) e    => optExp e
    | EPlus e1 e2           => EPlus (optExp e1) (optExp e2)
    | _                     => e
    end.

Fixpoint optCmd (c:Cmd) : Cmd :=
    match c with
    | CAssign v e   => CAssign v (optExp e)
    | CSeq c1 c2    => CSeq (optCmd c1) (optCmd c2)
    | CWhile e c    => CWhile (optExp e) (optCmd c)
    end. 

Lemma optExp_correct : forall (env:Env) (e:Exp), 
    evalExp env (optExp e) = evalExp env e. 
Proof.
    intros env. induction e as [n|v|e1 IH1 e2 IH2].
    - reflexivity.
    - reflexivity.
    - 


Show.
