Class Ordered (T : Type) :=
    { leq      : T -> T -> Prop
    ; leq_dec  : forall (s t:T), { leq s t } + {~ leq s t}
    ; eq_dec   : forall (s t:T), {s = t} + {~ s = t}
    ; leq_refl : forall (t:T), leq t t
    ; leq_trans: forall (s t r:T), leq s t -> leq t r -> leq s r
    ; leq_asym : forall (s t:T), leq s t -> leq t s -> s = t
    ; leq_total: forall (s t:T), leq s t \/ leq t s
    }.

Definition lt (T : Type) (Ord : Ordered T) (s t:T) : Prop :=
    match eq_dec s t with
    | left _    => False    (* s = t  *)
    | right _   => leq s t  (* s <> t *)
    end.

Arguments lt {T} {Ord}.

Lemma leq_lt_eq : forall (T:Type) (Ord:Ordered T) (s t:T), 
    leq s t <-> s = t \/ lt s t.
Proof.
    intros T Ord s t. split.
    - intros H. destruct (eq_dec s t) as [H'|H'] eqn:E.
        + left. assumption.
        + right. unfold lt. rewrite E. assumption.
    - intros [H|H].
        + rewrite H. apply leq_refl.
        + unfold lt in H. destruct (eq_dec s t) as [H'|H'] eqn:E.
            { contradiction. }
            { assumption. }
Qed.


Definition leq_total_dec : forall (T:Type) (Ord:Ordered T) (s t:T),
    {leq s t} + {leq t s}.
Proof.
    intros T Ord s t. destruct (leq_dec s t) as [H|H].
    - left. assumption.
    - right. destruct (leq_dec t s) as [H'|H'].
        + assumption.
        + remember (leq_total s t) as H1 eqn:E. clear E. destruct H1 as [H1|H1].
            { apply H in H1. contradiction. }
            { apply H' in H1. contradiction. }
Qed.

Arguments leq_total_dec {T} {Ord}.


