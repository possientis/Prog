Require Import List.

Inductive binop : Set := Plus | Times.

Inductive exp : Set :=
    | Const : nat -> exp
    | Binop : binop -> exp -> exp -> exp
    .


Definition binopDenote (b:binop) : nat -> nat -> nat :=
    match b with
        | Plus  => plus
        | Times => mult
    end.

Fixpoint expDenote (e:exp) : nat :=
    match e with
        | Const n       => n
        | Binop b e1 e2 => binopDenote b (expDenote e1) (expDenote e2)
    end.

Compute expDenote (Const 42).
Compute expDenote (Binop Plus (Const 2) (Const 3)).
Compute expDenote (Binop Times (Binop Plus (Const 2) (Const 3)) (Const 7)).


Inductive instr : Set :=
    | iConst : nat -> instr
    | iBinop : binop -> instr    
    .

Definition prog  := list instr.
Definition stack := list nat.

Definition instrDenote (i:instr)(s:stack) : option stack :=
    match i with
        | iConst n  => Some (n::s)
        | iBinop b  => 
            match s with
                | arg1 :: arg2 :: s' => Some (binopDenote b arg1 arg2 :: s') 
                | _                  => None
            end
    end.
             
Fixpoint progDenote (p:prog)(s:stack) : option stack :=
    match p with
        | nil   => Some s
        | i::p' => 
            match instrDenote i s with
                | None    => None
                | Some s' => progDenote p' s'
            end
    end.


Fixpoint compile (e:exp) : prog :=
    match e with
        | Const n       => iConst n :: nil
        | Binop b e1 e2 => compile e2 ++ compile e1 ++ iBinop b :: nil
    end.

Compute compile (Const 42).
Compute compile (Binop Plus (Const 2) (Const 3)).
Compute compile (Binop Times (Binop Plus (Const 2) (Const 3)) (Const 7)).

Compute progDenote (compile (Const 42)) nil.
Compute progDenote (compile (Binop Plus (Const 2) (Const 3))) nil.
Compute progDenote (
    compile (Binop Times (Binop Plus (Const 2) (Const 3)) (Const 7))) nil.


Lemma correctness' : forall e p s,
    progDenote (compile e ++ p) s = progDenote p (expDenote e :: s).
Proof.
    intros e. elim e.
    clear e. intros n p s. simpl. reflexivity.
    clear e. intros b. intros e1 H1 e2 H2 p s. simpl.
    rewrite app_assoc_reverse. rewrite H2.
    rewrite app_assoc_reverse. rewrite H1.
    simpl. reflexivity.
Qed.


Theorem correctness : forall e, 
    progDenote (compile e) nil = Some (expDenote e ::nil).
Proof.
    intros e. rewrite app_nil_end with (l:=compile e). apply correctness'.
Qed.

