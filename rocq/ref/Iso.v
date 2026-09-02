Open Scope type_scope.

Section Iso_axioms.

Variables A B C : Set.

Axiom Com : A * B = B * A.
Axiom Ass : A * (B * C) = A * B * C.
Axiom Cur : (A * B -> C) = (A -> B -> C).
Axiom Dis : (A -> B * C) = (A -> B) * (A -> C).
Axiom P_unit : A * unit = A.
Axiom AR_unit : (A -> unit) = unit.
Axiom AL_unit : (unit -> A) = A.

Lemma Cons : B = C -> A * B = A * C.
Proof.
    intros H. rewrite H. reflexivity.
Qed.

End Iso_axioms.

(* Need more recent version of coq it seems *)
Ltac simplify_type ty :=
    match ty with
    | ?A * ?B * ?C  => rewrite <- (Ass A B C); try simplify_type_eq
    end
with simplify_type_eq :=
    match goal with
    | |- ?A = ?B => try symplify_type A; try symplify_type B
    end.


