(* Living dangerously, Haskell notations ...                                    *)
Inductive Maybe (a:Set) (P:a -> Prop) : Set :=
| Nothing : Maybe a P
| Just    : forall (x:a), P x -> Maybe a P
.

Arguments Maybe {a} _.
Arguments Nothing {a} {P}.
Arguments Just {a} {P} {x} _.

Definition pred_strong (n:nat) :  Maybe (fun m => S m = n) :=
    match n with 
    | 0     => Nothing
    | S n   => Just (eq_refl (S n))
    end.

Definition maybe (a:Set) (P:a -> Prop) (def:a) (x:Maybe P) : a :=
    match x with
    | Nothing       => def
    | @Just _ _ y _ => y
    end.

Arguments maybe {a} {P} _ _.

Example pred_strong_test1 : maybe 0 (pred_strong 10) = 9.
Proof. reflexivity. Qed.


Example pred_strong_test2 : maybe 9 (pred_strong 0) = 9.
Proof. reflexivity. Qed.

(*
Compute (maybe 0 (pred_strong 10)).
*)

Notation "{{ x | P }}" := (Maybe (fun x => P)).
Notation "??"          := (Nothing).
Notation "[| x |]"     := (@Just _ _ x _).


Definition pred_strong' (n:nat) : {{m|S m = n}} :=
    match n return {{m | S m = n}} with  
    | 0     => ??
    | S n'   => @Just _ _ n' (eq_refl (S n')) 
    end.


Notation "x <- e1 ; e2" := (match e1 with 
                            | Nothing       => Nothing
                            | @Just _ _ x _ => e2
                            end)
(right associativity, at level 60).


Definition doublePred : forall (n1 n2:nat),  
    {{ p | n1 = S (fst p) /\ n2 = S (snd p) }}.
    refine (fun n1 n2 => 
        m1 <- pred_strong n1;
        m2 <- pred_strong n2;
        [|(m1,m2)|]). 
    split.
    - simpl. symmetry. assumption.
    - simpl. symmetry. assumption.
Defined.

(*
Print doublePred.
*)






