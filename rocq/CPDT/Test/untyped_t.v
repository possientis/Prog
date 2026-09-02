Require Import List.

Require Import untyped.

(*
Compute expDenote (Const 42).
Compute expDenote (Binop Plus (Const 2) (Const 3)).
Compute expDenote (Binop Times (Binop Plus (Const 2) (Const 3)) (Const 7)).
*)

Lemma expDenote_test1 : expDenote (Const 42) = 42.
Proof. reflexivity. Qed.

Lemma expDenote_test2 : expDenote (Binop Plus (Const 2) (Const 3)) = 5.
Proof. reflexivity. Qed.

Lemma expDenote_test3 : 
    expDenote (Binop Times (Binop Plus (Const 2) (Const 3)) (Const 7)) = 35.
Proof. reflexivity. Qed.


Lemma compile_test1 : compile (Const 42) = iConst 42 :: nil.
Proof. reflexivity. Qed.

Lemma compile_test2 : compile (Binop Plus (Const 2) (Const 3)) 
    = iConst 3 :: iConst 2 :: iBinop Plus :: nil
    .
Proof. reflexivity. Qed.

Lemma compile_test3 : 
    compile (Binop Times (Binop Plus (Const 2) (Const 3)) (Const 7)) 
  = iConst 7 :: iConst 3 :: iConst 2 :: iBinop Plus :: iBinop Times :: nil
    .
Proof. reflexivity. Qed.

Lemma eval_test1 : eval (Const 42) = Some 42.
Proof. reflexivity. Qed.

Lemma eval_test2 : eval (Binop Plus (Const 2) (Const 3)) = Some 5.
Proof. reflexivity. Qed.
    
Lemma eval_test3 : 
    eval (Binop Times (Binop Plus (Const 2) (Const 3)) (Const 7)) = Some 35.
Proof. reflexivity. Qed.



