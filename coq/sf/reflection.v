Require Import nat.
Require Import bool.
Require Import induction.

(* direct proof *)
Example even_1000 : exists k, 1000 = double k.
Proof. exists 500. reflexivity. Qed.

(* at boolean level, even simpler *)
Example even_1000': evenb 1000 = true.
Proof. reflexivity. Qed.

(* transporting proof to boolean level *)
Example even_1000'' : exists k, 1000 = double k.
Proof. apply even_bool_prop. reflexivity. Qed.


