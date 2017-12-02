Inductive ev : nat -> Prop :=
    | ev_0  : ev 0
    | ev_SS : forall (n:nat), ev n -> ev (S (S n))
    . 

Theorem ev_4 : ev 4.
Proof. apply ev_SS. apply ev_SS. exact ev_0. Qed.

Theorem ev_4' : ev 4.
Proof. exact (ev_SS 2 (ev_SS 0 ev_0)). Qed.

