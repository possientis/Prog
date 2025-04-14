Require Import List.

Lemma arith_comm : forall (a:Type) (l m:list a),
    length l = length m \/ length l + length m = 6 ->
    length (l ++ m) = 6 \/ length l = length m.
Proof.
    intuition. left. rewrite app_length. assumption. 
Qed.




