Class Ordered (T : Type) :=
    { leq      : T -> T -> Prop
    ; leq_dec  : forall (s t:T), { leq s t } + {~ leq s t}
    ; eq_dec   : forall (s t:T), {s = t} + {~ s = t}
    ; leq_refl : forall (t:T), leq t t
    ; leq_trans: forall (s t r:T), leq s t -> leq t r -> leq s r
    ; leq_asym : forall (s t:T), leq s t -> leq t s -> s = t
    ; leq_total: forall (s t:T), leq s t \/ leq t s
    }.

Notation "s <= t" := (leq s t) (at level 70) : Ordered_scope. 
Open Scope Ordered_scope.


Definition lt (T : Type) (Ord : Ordered T) (s t:T) : Prop :=
    match eq_dec s t with
    | left _    => False    (* s = t  *)
    | right _   => s <= t   (* s <> t *)
    end.

Arguments lt {T} {Ord}.
Notation "s < t" := (lt s t) (at level 70) : Ordered_scope.


Lemma leq_is_eq_or_lt : forall (T:Type) (Ord:Ordered T) (s t:T), 
    s <= t <-> s = t \/ s < t.
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
    {s <= t} + {t <= s}.
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


Definition lt_dec : forall (T:Type) (Ord:Ordered T) (s t:T),
    {s < t} + {~ s < t}.
Proof.
    intros T Ord s t.
    destruct (eq_dec s t) as [H|H] eqn:E.
    - subst. right. unfold lt. rewrite E. intros H. contradiction.
    - destruct (leq_dec s t) as [H'|H'].
        + left. unfold lt. rewrite E. assumption.
        + right. unfold lt. rewrite E. assumption.
Qed.

Arguments lt_dec {T} {Ord}.

Definition trichotomy : forall (T:Type) (Ord:Ordered T) (s t:T),
    {s < t} + {s = t} + {t < s}.    (* left associative *)
Proof.
    intros T Ord s t. destruct (lt_dec s t) as [H|H].
    - left. left. assumption.
    - destruct (eq_dec s t) as [H'|H'] eqn:E.
        + left. right. assumption.
        + right. unfold lt. destruct (eq_dec t s) as [H1|H1]. 
            { subst. apply H'. reflexivity. }
            { destruct (leq_total_dec s t) as [H2|H2].
                { exfalso. apply H. unfold lt. rewrite E. assumption. }
                { assumption. }}
Qed.
