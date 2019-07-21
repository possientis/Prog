Definition monotone (a:Type) (f:nat -> option a) : Prop :=
    forall (n:nat) (v:a), f n = Some v -> 
    forall (m:nat), n <= m -> f m = Some v.

Arguments monotone {a} _.

Definition Computation (a:Type) : Type := { f:nat -> option a | monotone f }.


(* Expresses the fact that computation k yields value v for input n             *)
Definition runTo (a:Type) (k:Computation a) (n:nat) (v:a) : Prop :=
    proj1_sig k n = Some v.

Arguments runTo {a} _ _ _.

(* Expresses the fact that computation k eventually yields v                    *) 
Definition run (a:Type) (k:Computation a) (v:a) : Prop :=
    exists (n:nat), runTo k n v.

Arguments run {a} _ _.

(* We are defining a value with coq tactics. This makes a lot of sense because  *)
(* the value we are defining is essentially a tuple where the second coordinate *)
(* is a proof, so using tactics makes a lot of sense. Note that this proof is   *)
(* not opaque ('Defined' rather than 'Qed'). Alternatively, we could have       *)
(* defined the proof separately as some sort of lemma and defined the value     *)
(* 'bot' in the usual direct way by referring to this lemma                     *)
Definition bot (a:Type) : Computation a.
    unfold Computation. exists (fun (_:nat) => None).
    unfold monotone. intros n v H. inversion H.
Defined.

Arguments bot {a}.

(* 'return' is a keyword in coq, so using 'pure' instead                        *)
Definition pure (a:Type) : a -> Computation a.
    intros v. 
    unfold Computation. exists (fun (_:nat) => Some v).
    unfold monotone. intros n w H. inversion H. subst.
    intros m H'. reflexivity.
Defined.

Arguments pure {a} _.

Lemma run_pure : forall (a:Type) (v:a), run (pure v) v. 
Proof.
    intros a v. unfold run. exists 0. reflexivity.
Qed.

Definition bind(a b:Type)(k:Computation a)(g:a -> Computation b):Computation b.
    unfold Computation. 
    remember (fun (n:nat) =>
        match proj1_sig k n with
        |   Some va => proj1_sig (g va) n
        |   None    => None
        end) as gf eqn:GF.
    exists gf.
    unfold monotone. 
    intros n vb H m I.
    destruct k as [f Mf]. simpl in GF. 
    unfold monotone in Mf.
    rewrite GF in H. rewrite GF.
    destruct (f n) as [va|] eqn:Fn.
        - destruct (f m) as [va'|] eqn:Fm.
            + assert (f m = Some va) as E. 
                { apply Mf with n; assumption. }
              rewrite Fm in E. inversion E.
              destruct (g va) as [g' Mg']. simpl. simpl in H.
              unfold monotone in Mg'. apply Mg' with n; assumption.
            + assert (f m = Some va) as E.
                { apply Mf with n; assumption. }
              rewrite Fm in E. inversion E.
        - inversion H.
Defined.

Arguments bind {a} {b} _ _.


Notation "k >>= g" := (bind k g) (at level 50).

(*
Lemma run_bind : forall (a b:Type) (k:Computation a) (g:a -> Computation b),
    forall (x:a) (y:b), run k x -> run (g x) y -> run (k >>= g) y.
Proof.


Show.
*)


