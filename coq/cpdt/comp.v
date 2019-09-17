CoInductive Comp (a:Type) : Type :=
| Ret : a -> Comp a
| Bnd : forall (a':Type), Comp a' -> (a' -> Comp a) -> Comp a
.

Arguments Ret {a}.
Arguments Bnd {a} {a'}.

(* Usual trick for coinductive type                                             *)
Definition frob (a:Type) (c:Comp a) : Comp a :=
    match c with
    | Ret x     => Ret x
    | Bnd c f   => Bnd c f
    end.

Arguments frob {a}.

Lemma frob_same : forall (a:Type) (c:Comp a), c = frob c.
Proof. intros a [x|a' c f]; reflexivity. Qed.

(* Need to pick some good notion of equality with coinductive proofs            *)
CoInductive comp_eq (a:Type) : Comp a -> Comp a -> Prop :=
| Ret_eq : forall (x:a), comp_eq a (Ret x) (Ret x) 
| Bnd_eq : forall (a':Type) (c1 c2:Comp a') (f1 f2:a' -> Comp a), 
    comp_eq a' c1 c2                        -> 
    (forall (z:a'), comp_eq a (f1 z) (f2 z))  ->
    comp_eq a (Bnd c1 f1) (Bnd c2 f2)
.

Arguments comp_eq {a}.

Lemma comp_eq_ret : forall (a:Type) (x y:a), comp_eq (Ret x) (Ret y) -> x = y.
Proof.
    intros a x y H. inversion H. reflexivity.
Qed.

Lemma comp_eq_refl : forall (a:Type) (c:Comp a), comp_eq c c.
Proof.
    cofix. intros a [x|a' c f].
    - constructor.
    - constructor.
        + apply comp_eq_refl.
        + intros z. apply comp_eq_refl.
Qed.

Lemma comp_eq_sym : forall (a:Type) (c1 c2:Comp a), 
    comp_eq c1 c2 -> comp_eq c2 c1.
Proof.
    cofix. intros a c1 c2 H. 
    destruct H as [|a' c1 c2 f1 f2 H1 H2].
    - constructor.
    - constructor. 
        + apply comp_eq_sym. assumption.
        + intros z. apply comp_eq_sym. apply H2.
Qed.

(*
Lemma comp_eq_trans : forall (a:Type) (c1 c2 c3:Comp a),
    comp_eq c1 c2 -> comp_eq c2 c3 -> comp_eq c1 c3.
Proof.
    cofix. intros a c1 c2 c3 H. revert c3.
    destruct H as [|a' c1 c2 f1 f2 H1 H2].
    - intros c3 H. assumption.
    - intros c3 H3. remember (Bnd c2 f2) as c2' eqn:E. revert E.
      destruct H3 as [|a'' c2' c3 f2' f3 H4 H5].
        + intros H3. inversion H3.
        + intros H3. 


Show.
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
