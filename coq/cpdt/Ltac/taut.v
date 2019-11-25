Inductive Taut : Set :=
| TautTrue : Taut
| TautAnd  : Taut -> Taut -> Taut
| TautOr   : Taut -> Taut -> Taut
| TautImp  : Taut -> Taut -> Taut
.


Fixpoint tautDenote (t:Taut) : Prop :=
    match t with
    | TautTrue      => True
    | TautAnd t1 t2 => tautDenote t1 /\ tautDenote t2
    | TautOr  t1 t2 => tautDenote t1 \/ tautDenote t2
    | TautImp t1 t2 => tautDenote t1 -> tautDenote t2
    end.

Lemma tautTrue : forall (t:Taut), tautDenote t.
Proof.
    induction t as [|t1 IH1 t2 IH2|t1 IH1 t2 IH2|t1 IH1 t2 IH2].
    - constructor.
    - split; assumption.
    - left. assumption.
    - simpl. intros _. assumption.
Qed.

Ltac tautReify P :=
    match P with
    | True  => TautTrue
    | ?P1 /\ ?P2 =>
        let t1 := tautReify P1 in
        let t2 := tautReify P2 in
            constr:(TautAnd t1 t2)
    | ?P1 \/ ?P2 =>
        let t1 := tautReify P1 in
        let t2 := tautReify P2 in
            constr:(TautOr t1 t2)
    | ?P1 -> ?P2 =>
        let t1 := tautReify P1 in
        let t2 := tautReify P2 in
            constr:(TautImp t1 t2)
    end.

Ltac obvious :=
    match goal with
    | [|- ?P ] =>
        let t := tautReify P in
            exact (tautTrue t)
    end.

Lemma true_galore : (True /\ True) -> (True \/ (True /\ (True -> True))).
Proof. tauto. Qed.

(*
Print true_galore.

true_galore = 
fun H : True /\ True => and_ind (fun _ _ : True => or_introl I) H
     : True /\ True -> True \/ True /\ (True -> True)
*)


Lemma true_galore' : (True /\ True) -> (True \/ (True /\ (True -> True))).
Proof. obvious. Qed.

(*
Print true_galore'.

true_galore' = 
tautTrue
  (TautImp (TautAnd TautTrue TautTrue)
       (TautOr TautTrue (TautAnd TautTrue (TautImp TautTrue TautTrue))))
            : True /\ True -> True \/ True /\ (True -> True)
*)


