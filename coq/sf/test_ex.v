Require Import nat.
Require Import inductive_prop.


Definition some_nat_is_even : ex ev := ex_intro ev 0 ev_0.
Definition some_nat_is_even': ex ev := ex_intro ev 4 (ev_SS 2 (ev_SS 0 ev_0)).


Definition ex_ev_Sn : ex (fun n => ev (S n)) := 
    ex_intro (fun n => ev (S n)) 1 (ev_SS 0 ev_0).

