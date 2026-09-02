Print Empty_set. (* Inductive Empty_set : Set := *)


Inductive strange : Set := cs: strange-> strange. (* empty type *)

Check strange_ind. 
(* forall P : strange -> Prop,
  (forall s : strange, P s -> P (cs s)) -> forall s : strange, P s *)


Theorem strange_empty : forall x:strange, False.
Proof.
  intro x. elim x. trivial. 
Qed.

Theorem empty_set : forall P : Empty_set -> Prop, forall x:Empty_set, P x.
Proof.
  intros P x. elim x.
Qed.

Inductive even_line : nat -> Set :=
  | even_empty_line : even_line 0
  | even_step_line  : forall (n:nat), even_line n -> even_line (S (S n)).


Check even_empty_line.                  (* : even_line 0 *)
Check even_step_line _ even_empty_line. (* even_line 2 *) (* first argument implicitly deduced *)


