Require Import Coq.Lists.List.

Inductive binop : Set := 
| Plus  : binop
| Times : binop
.

Inductive exp : Set :=
| Const : nat -> exp
| Binop : binop -> exp-> exp -> exp
.

Definition binopDenote (b:binop) : nat -> nat -> nat :=
    match b with 
    | Plus  => plus
    | Times => mult
    end.

(* type inference at play *) 
Definition binopDenote' := fun b => 
    match b with
    | Plus  => plus
    | Times => mult
    end.

Fixpoint expDenote (e:exp) : nat :=
    match e with
    | Const n       => n
    | Binop b e1 e2 => binopDenote b (expDenote e1) (expDenote e2)
    end.

(*
Compute expDenote (Const 42).
Compute expDenote (Binop Plus (Const 2) (Const 3)).
Compute expDenote (Binop Times (Binop Plus (Const 2) (Const 3)) (Const 7)).
*)

Lemma expDenote_test1 : expDenote (Const 42) = 42.
Proof. reflexivity. Qed.

Lemma expDenote_test2 : expDenote (Binop Plus (Const 2) (Const 3)) = 5.
Proof. reflexivity. Qed.

Lemma expDenote_test3 : expDenote (Binop Times (Binop Plus (Const 2) (Const 3)) (Const 7)) = 35.
Proof. reflexivity. Qed.

Inductive instr : Set :=
| iConst : nat   -> instr
| iBinop : binop -> instr
.

Definition prog  : Set := list instr.
Definition stack : Set := list nat.

Definition instrDenote (i:instr) (s:stack) : option stack :=
    match i with
    | iConst n  => Some (n :: s)
    | iBinop b  => 
        match s with
        | x1 :: x2 :: s'    => Some ((binopDenote b) x1 x2 :: s')
        | _                 => None
        end
    end.

Fixpoint progDenote (p:prog) (s:stack) : option stack :=
    match p with
    | nil       => Some s
    | i :: q    => 
        match instrDenote i s with
        | None      => None
        | Some s'   => progDenote q s'
        end
    end.

Fixpoint compile (e:exp) : prog :=
    match e with
    | Const n       => iConst n :: nil
    | Binop b e1 e2 => compile e2 ++ compile e1 ++ iBinop b :: nil
    end.


Lemma compile_test1 : compile (Const 42) = iConst 42 :: nil.
Proof. reflexivity. Qed.

Lemma compile_test2 : compile (Binop Plus (Const 2) (Const 3)) 
    = iConst 3 :: iConst 2 :: iBinop Plus :: nil
    .
Proof. reflexivity. Qed.

Lemma compile_test3 : compile (Binop Times (Binop Plus (Const 2) (Const 3)) (Const 7)) 
    = iConst 7 :: iConst 3 :: iConst 2 :: iBinop Plus :: iBinop Times :: nil
    .
Proof. reflexivity. Qed.

Definition eval (e:exp) : option nat :=
    match progDenote (compile e) nil with
    | Some (n::nil) => Some n
    | _             => None
    end.

Lemma eval_test1 : eval (Const 42) = Some 42.
Proof. reflexivity. Qed.

Lemma eval_test2 : eval (Binop Plus (Const 2) (Const 3)) = Some 5.
Proof. reflexivity. Qed.
    
Lemma eval_test3 : eval (Binop Times (Binop Plus (Const 2) (Const 3)) (Const 7)) = Some 35.
Proof. reflexivity. Qed.


Lemma compile_correct' : forall (e:exp) (p:prog) (s:stack),
    progDenote (compile e ++ p) s = progDenote p (expDenote e :: s).
Proof.
    intros e. induction e as [n|b e1 H1 e2 H2]; intros p s; simpl.
    - reflexivity.
    - rewrite app_assoc_reverse. rewrite H2. 
      rewrite app_assoc_reverse. rewrite H1.
      reflexivity.
Qed.

Theorem compile_correct : forall (e:exp), eval e = Some (expDenote e).
Proof.
    intros e. unfold eval. rewrite <- (app_nil_r (compile e)).
    rewrite compile_correct'. reflexivity.
Qed.


