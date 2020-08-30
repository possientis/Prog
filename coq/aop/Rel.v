Definition R (a:Type) (b:Type) : Type := a -> b -> Prop.

Definition eqRel (a b:Type) (r s:R a b) : Prop :=
    forall (x:a) (y:b), r x y <-> s x y.

Arguments eqRel {a} {b}.

Notation "r == s" := (eqRel r s)
    (at level 60, right associativity) : Rel_scope.

Open Scope Rel_scope.

Inductive id (a:Type) : R a a :=
| refl : forall (x:a), id a x x
.

Arguments id {a}.

Lemma id_charac : forall (a:Type) (x y:a),
    id x y <-> x = y.
Proof.
    intros a x y. split; intros H1.
    - destruct H1. reflexivity.
    - rewrite H1. constructor.
Qed.

(*
Definition comp (a b c:Type) (s:R b c) (r:R a b) : R a c :=
    fun (x:a) (z:c) => exists (y:b), r x y /\ s y z.

Arguments comp {a} {b} {c}.

Notation "s ; r" := (comp s r) 
    (at level 60, right associativity) : Rel_scope.

Open Scope Rel_scope.
*)

