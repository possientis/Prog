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
    unfold Computation. exists (fun (_:nat) => @None a).
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


Definition bind(a b:Type)(k:Computation a)(g:a -> Computation b):Computation b.
    destruct k as [f p].
    remember ( fun (n:nat) =>
        match f n with
        | Some v    => proj1_sig (g v) n
        | None      => @None b
        end) as h eqn:H.
    unfold Computation. exists h.
    unfold monotone. intros n v E m H'.
    destruct (f n) as [w q|H1] eqn:H2.
        - rewrite H in E. rewrite H2 in E. rewrite H.
          destruct (f m) as [x r|I1] eqn:I2.
          + unfold monotone in p.


Show.
