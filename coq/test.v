Require Import Bool Arith List CpdtTactics.
Set Implicit Arguments.

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


Theorem compile_correct : forall e, 
  progDenote (compile e) nil = Some (expDenote e :: nil).


Abort.


Lemma compile_correct' : forall e p s,
  progDenote (compile e ++ p) s = progDenote p (expDenote e :: s).

  induction e.
  intros.
  unfold compile.
  unfold expDenote.
  unfold progDenote at 1.
  simpl.
  fold progDenote.
  reflexivity.

  intros.
  unfold compile.
  fold compile.
  unfold expDenote.
  fold expDenote.
(*
Check app_assoc_reverse.
Check app_assoc.
SearchRewrite((_++_)++_).
*)
  rewrite app_assoc_reverse.
  rewrite IHe2.
  rewrite app_assoc_reverse.
  rewrite IHe1.
  unfold progDenote at 1.
  simpl.
  fold progDenote. 
  reflexivity.

Abort.

Lemma compile_correct' : forall e p s,
  progDenote (compile e ++ p) s = progDenote p (expDenote e :: s).

  induction e; crush.
Qed.

Theorem compile_correct : forall e, 
  progDenote (compile e) nil = Some (expDenote e :: nil).
 
  intros.

(*
Check app_nil_end.
*)
  rewrite (app_nil_end(compile e)).
  rewrite compile_correct'.
  unfold progDenote. (* actually this is optional, as reflexivity will check *)
  reflexivity.
Qed.

Inductive type : Set := Nat | Bool.

Inductive tbinop : type -> type -> type -> Set :=
| TPlus : tbinop Nat Nat Nat
| TTimes : tbinop Nat Nat Nat
| TEq : forall t, tbinop t t Bool
| TLt : tbinop Nat Nat Bool.

Inductive texp : type -> Set :=
| TNConst : nat -> texp Nat
| TBConst : bool -> texp Bool
| TBinop : forall t1 t2 t, tbinop t1 t2 t -> texp t1 -> texp t2 -> texp t.

Definition typeDenote (t : type) : Set :=
  match t with
    | Nat => nat
    | Bool => bool
  end.

Definition tbinopDenote arg1 arg2 res (b : tbinop arg1 arg2 res)
  : typeDenote arg1 -> typeDenote arg2 -> typeDenote res :=
  match b with
    | TPlus => plus
    | TTimes => mult
    | TEq Nat => beq_nat
    | TEq Bool => eqb
    | TLt => leb
  end.

Fixpoint texpDenote t (e : texp t) : typeDenote t :=
  match e with
    | TNConst n => n
    | TBConst b => b
    | TBinop _ _ _ b e1 e2 => (tbinopDenote b) (texpDenote e1) (texpDenote e2)
  end.

Definition texp1: texp Nat  := TNConst 42.
Definition texp2: texp Bool := TBConst false.
Definition texp3: texp Bool := TBConst true.
Definition texp_2p2         := TBinop TPlus (TNConst 2) (TNConst 2).
Definition texp_7           := TNConst 7.
Definition texp4: texp Nat  := TBinop TTimes texp_2p2 texp_7.
Definition texp5: texp Bool := TBinop (TEq Nat) texp_2p2 texp_7.
Definition texp6: texp Bool := TBinop TLt texp_2p2 texp_7.



(*
Eval simpl in texpDenote texp1. 
Eval simpl in texpDenote texp2. 
Eval simpl in texpDenote texp3. 
Eval simpl in texpDenote texp4. 
Eval simpl in texpDenote texp5. 
Eval simpl in texpDenote texp6. 
*)




