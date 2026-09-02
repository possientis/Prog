Lemma symmetry : forall (a b:Type), a = b -> b = a.
Proof.
    intros a b H. rewrite H. reflexivity.
Qed.

Set Printing All.
(*
Lemma silly : unit = unit.
Proof.

    apply symmetry.
Abort.
*)
Unset Printing All.

