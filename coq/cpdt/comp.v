CoInductive Comp (a:Type) : Type :=
| Ret : a -> Comp a
| Bnd : forall (a':Type), Comp a' -> (a' -> Comp a) -> Comp a
.

Arguments Ret {a}.
Arguments Bnd {a} {a'}.

Definition cast (a b:Type) (p:a = b) (x:a) : b :=
    match p with
    | eq_refl   => x
    end.

Arguments cast {a} {b}.

Lemma Bnd_injective_type : 
forall (a1 a2 a:Type) (c1:Comp a1) (c2:Comp a2) (f1:a1 -> Comp a) (f2:a2 -> Comp a),
    Bnd c1 f1 = Bnd c2 f2 -> a1 = a2.
Proof. intros a1 a2 a c1 c2 f1 f2 H. inversion H. reflexivity. Qed.

Lemma Bnd_injective_type1 : 
forall (a1 a2 a:Type) (c1:Comp a1) (c2:Comp a2) (f1:a1 -> Comp a) (f2:a2 -> Comp a),
    Bnd c1 f1 = Bnd c2 f2 -> Comp a1 = Comp a2.
Proof.
    intros a1 a2 a c1 c2 f1 f2 H. assert (a1 = a2) as E.
        { apply (Bnd_injective_type a1 a2 a c1 c2 f1 f2). assumption. }
    rewrite E. reflexivity.
Qed.

Lemma Bnd_injective_type2 : 
forall (a1 a2 a:Type) (c1:Comp a1) (c2:Comp a2) (f1:a1 -> Comp a) (f2:a2 -> Comp a),
    Bnd c1 f1 = Bnd c2 f2 -> (a1 ->  Comp a) = (a2 -> Comp a).
Proof.
    intros a1 a2 a c1 c2 f1 f2 H. assert (a1 = a2) as E.
        { apply (Bnd_injective_type a1 a2 a c1 c2 f1 f2). assumption. }
    rewrite E. reflexivity.
Qed.
(*
Lemma Bnd_injective_type1' : 
forall (a1 a2 a:Type) (c1:Comp a1) (c2:Comp a2) (f1:a1 -> Comp a) (f2:a2 -> Comp a),
forall (p:Bnd c1 f1 = Bnd c2 f2),
    c2 = cast (Bnd_injective_type1 a1 a2 a c1 c2 f1 f2 p) c1.
Proof.
    intros a1 a2 a c1 c2 f1 f2 p. remember (Bnd_injective_type a1 a2 a c1 c2 f1 f2 p) as q eqn:E.
    subst.
*)
(*
Inductive Exec (a:Type) : Comp a -> a -> Prop :=
| ExecRet : forall (x:a), Exec a (Ret x) x
| ExecBnd : forall (a':Type) (c:Comp a')(f:a' -> Comp a) (x:a') (y:a),
    Exec a' c x -> Exec a (f x) y -> Exec a (Bnd c f) y
. 

Arguments Exec {a}.

Definition comp_eq (a:Type) (c1 c2:Comp a) : Prop :=
    forall (x:a), Exec c1 x <-> Exec c2 x.

Arguments comp_eq {a}.

Lemma comp_eq_refl : forall (a:Type) (c:Comp a) , comp_eq c c.
Proof. unfold comp_eq. intros a c x. split; intros H; assumption. Qed.

Lemma comp_eq_sym : forall (a:Type) (c1 c2:Comp a), 
    comp_eq c1 c2 -> comp_eq c2 c1.
Proof.
    unfold comp_eq. intros a c1 c2 H x. split; intros H'; apply H; assumption.
Qed.

Lemma comp_eq_trans : forall (a:Type) (c1 c2 c3:Comp a),
    comp_eq c1 c2 -> comp_eq c2 c3 -> comp_eq c1 c3.
Proof.
    unfold comp_eq. intros a c1 c2 c3 H1 H2 x. split; intros H.
    - apply H2, H1. assumption.
    - apply H1, H2. assumption.
Qed.

Definition pure (a:Type) (x:a) : Comp a := Ret x.

Arguments pure {a}.

Definition bind (a b:Type) (k:Comp a) (f:a -> Comp b) : Comp b := Bnd k f.

Arguments bind {a} {b}.

Notation "k >>= f" := (bind k f) (at level 50, left associativity).

Notation "c1 == c2" := (comp_eq c1 c2) (at level 90).
*)

(*
Lemma left_identity : forall (a b:Type) (x:a) (f:a -> Comp b),
    (pure x) >>= f == f x.
Proof.
    intros a b x f y. split.
    - intros H. remember (pure x >>= f) as k eqn:E. revert E. 
      destruct H as [x'|a' c g x' y' H1 H2]; intros H.
        + inversion H.
        + unfold bind in H. revert H1 H2. remember (pure x) as k eqn:E. revert E.  


Show.
*)
