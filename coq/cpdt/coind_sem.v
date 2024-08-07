Require Import Arith.

Definition Var := nat.

Definition Env := Var -> nat.

Definition empty : Env := fun v => 0.

Definition update (env:Env) (v:Var) (n:nat) : Env :=
    fun (x:Var) => if Nat.eqb x v then n else env x.

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
    intros R H1 H2 H3. cofix coIH. intros e1 e2 c H. destruct c.
    - apply H1 in H. rewrite H. constructor.
    - rename e2 into e3. apply H2 in H. destruct H as [e2 [H12 H23]].
      apply EvalSeq with e2; apply coIH; assumption.
    - rename e2 into e3. apply H3 in H. destruct H as [H|H].
        + destruct H as [E1 E2]. subst. apply EvalWhileFalse. assumption.
        + destruct H as [e2 [E1 [E2 E3]]]. apply EvalWhileTrue with e2.
            { assumption. }
            { apply coIH. assumption. }
            { apply coIH. assumption. }
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
    - destruct e1 as [n1|v1|e1' e2']. 
        + destruct n1 as [|n1].
            { simpl. assumption. }
            { simpl. rewrite IH2. reflexivity. }
        + simpl. rewrite IH2. reflexivity.
        + simpl in IH1. simpl. rewrite IH1, IH2. reflexivity. 
Qed.


Lemma optCmd_correct1 : forall (e1 e2:Env) (c:Cmd),
    evalCmd e1 c e2 -> evalCmd e1 (optCmd c) e2.
Proof.
    intros e1 e2 c H.
    apply (evalCmd_coind (fun e1 c' e2 => 
        exists c, c' = optCmd c /\ evalCmd e1 c e2)). 
    - clear e1 e2 c H. intros e1 e2 e v [c [H1 H2]]. revert e v H1.
      destruct H2.
        + intros e' v' H. simpl in H. inversion H. subst.
          rewrite optExp_correct. reflexivity.
        + intros e v H. simpl in H. inversion H.
        + intros e' v H'. simpl in H'. inversion H'.
        + intros e' v H'. simpl in H'. inversion H'.
    - clear e1 e2 c H. intros e1 e3 c1 c2 [c [H1 H2]].
      revert c1 c2 H1. destruct H2.
        + intros c1 c2 H. simpl in H. inversion H.
        + intros c3 c4 H. simpl in H. inversion H. subst.
          exists e2. split.
            { exists c1. split. { reflexivity. } { assumption. } }
            { exists c2. split. { reflexivity. } { assumption. } }
        + intros c1 c2 H'. simpl in H'. inversion H'.
        + intros c1 c2 H'. simpl in H'. inversion H'.
    - clear e1 e2 c H. intros e1 e3 e c [c' [H1 H2]].
      revert e c H1. destruct H2.     
        + intros e' c H. simpl in H. inversion H.
        + intros e c H. simpl in H. inversion H.
        + intros e' c' H'. simpl in H'. inversion H'. subst.
          left. split. 
            { rewrite optExp_correct. assumption. }
            { reflexivity. }
        + intros e' c' H'. simpl in H'. inversion H'. subst. right.
          exists e2. split.
            { rewrite optExp_correct. assumption. }
            { split.
                { exists c. split. { reflexivity. } { assumption. }}
                { exists (CWhile e c). split. { reflexivity. } { assumption. }}}
    - exists c. split. 
        + reflexivity.
        + assumption.
Qed.

Lemma optCmd_correct2 : forall (e1 e2:Env) (c:Cmd),
    evalCmd e1 (optCmd c) e2 -> evalCmd e1 c e2.
Proof.
    apply (evalCmd_coind (fun e1 c e2 => evalCmd e1 (optCmd c) e2)).
    -  intros e1 e2 e v H. simpl in H.
       remember (CAssign v (optExp e)) as c' eqn:E. 
       revert e v E. destruct H.
        + intros e' v' H. inversion H. subst. clear H.
          rewrite optExp_correct. reflexivity.
        + intros e v H'. inversion H'.
        + intros e' v H'. inversion H'.
        + intros e' v H'. inversion H'.
    - intros e1 e3 c1 c2 H. simpl in H.
      remember (CSeq (optCmd c1) (optCmd c2)) as c' eqn:E.
      revert c1 c2 E. destruct H.
        + intros c1 c2 H. inversion H.
        + intros c1' c2' H'. inversion H'. subst. clear H'. exists e2. split; assumption.
        + intros c1 c2 H'. inversion H'.
        + intros c1 c2 H'. inversion H'.
    - intros e1 e3 e c H. simpl in H.
      remember (CWhile (optExp e) (optCmd c)) as c' eqn:E.
      revert e c E. destruct H.
        + intros e' c H. inversion H.
        + intros e c H'. inversion H'.
        + intros e' c' H'. inversion H'. subst. clear H'. left. split.
            { rewrite optExp_correct in H. assumption. }
            { reflexivity. }
        + intros e' c' H'. inversion H'. subst. clear H'. right. exists e2. split.
            { rewrite optExp_correct in H. assumption. }
            { split; assumption. }
Qed.

Theorem optCmd_correct : forall (e1 e2:Env) (c:Cmd), 
    evalCmd e1 (optCmd c) e2 <-> evalCmd e1 c e2.
Proof. 
    intros e1 e2 c. split.
    - apply optCmd_correct2.
    - apply optCmd_correct1.
Qed.


