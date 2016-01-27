Require Import List.
(*
Require Import Bool Arith List CpdtTactics. 
*)
(*
Set Implicit Arguments.
*)
(*
Set Asymetric Patterns. (* no impact before Coq version 8.5 *)
*) 

Inductive binop : Set := Plus | Times.

Inductive exp : Set :=
| Const : nat -> exp
| Binop : binop -> exp -> exp -> exp.

(*
Definition binopDenote (b : binop) : nat -> nat -> nat :=
  match b with
  | Plus => plus
  | Times => mult
  end.
*)

(*
Definition binopDenote : binop -> nat -> nat -> nat := fun (b : binop) =>
  match b with
  | Plus => plus
  | Times => mult
  end.
*)

Definition binopDenote := fun b =>
  match b with
    | Plus => plus
    | Times => mult
  end.

Fixpoint expDenote (e : exp) : nat :=
  match e with
    | Const n => n
    | Binop b e1 e2 => (binopDenote b) (expDenote e1 ) (expDenote e2 )
  end.

Definition exp1 : exp := Const 42.
Definition exp2 : exp := Binop Plus (Const 2) (Const 2).
Definition exp3 : exp := Binop Times exp2 (Const 7).

(*
Eval simpl in expDenote exp1.
Eval simpl in expDenote exp2.
Eval simpl in expDenote exp3.
*)


(*
Eval simpl in expDenote(Binop Times (Binop Plus (Const 2) (Const 2)) (Const 7)).
*)

Inductive instr : Set :=
| iConst : nat -> instr
| iBinop : binop -> instr.

Definition prog := list instr.
Definition stack := list nat.

Definition instrDenote (i : instr) (s : stack) : option stack :=
  match i with
    | iConst n => Some (n :: s)
    | iBinop b =>
      match s with
        | arg1 :: arg2 :: s' => Some ((binopDenote b) arg1 arg2 :: s')
        | _ => None
      end
  end.

Fixpoint progDenote (p : prog) (s : stack) : option stack :=
  match p with
    | nil     => Some s
    | i :: p' =>
      match instrDenote i s with
        | None    => None
        | Some s' => progDenote p' s'
      end
    end.

Fixpoint compile (e : exp) : prog :=
  match e with
    | Const n       => iConst n :: nil
    | Binop b e1 e2 => compile e2 ++ compile e1 ++ iBinop b :: nil
  end.

(*
Eval simpl in compile exp1. (* Const 42 *)
Eval simpl in compile exp2. (* Binop Plus (Const 2) (Const 2) *)
Eval simpl in compile exp3. (* Binop Times (Binop Plus (Const 2) (Const 2)) (Const 7) *)
*)

Definition prog1 : prog := compile exp1.
Definition prog2 : prog := compile exp2.
Definition prog3 : prog := compile exp3.

(*
Eval simpl in progDenote prog1 nil.
Eval simpl in progDenote prog2 nil.
Eval simpl in progDenote prog3 nil.
*)






