Parameter A : Type.
Parameter eq_bool : A -> A -> bool.
Axiom eq_bool_true : forall (x y:A), eq_bool x y = true  -> x = y.
Axiom eq_bool_false: forall (x y:A), eq_bool x y = false -> x <> y.


(* convoy pattern *)
Definition test (x y:A) : {x = y} + {x <> y} :=
    match eq_bool x y as b return eq_bool x y = b -> {x = y} + {x <> y} with
    | true  => fun p    => left  (eq_bool_true  x y p)
    | false => fun p    => right (eq_bool_false x y p)
    end (eq_refl (eq_bool x y)).

(* we do not need to use the convoy pattern *) 

Definition test_bool (b:bool) : {b = true} + {b = false} :=
    match b with
    | true  => left  (eq_refl true)
    | false => right (eq_refl false)
    end.

(* now do not pattern match on boolean values, but on proofs instead *)

Definition test' (x y:A) : {x = y} + {x <> y} :=
    match test_bool (eq_bool x y) with
    | left  p   => left  (eq_bool_true  x y p)
    | right p   => right (eq_bool_false x y p)
    end.


(* functions such as test and test' are always 'correct' *)
Definition correct (f:forall (x y:A), {x = y} + {x <> y}) : Prop := 
    forall (x y:A),
        ( (exists p, f x y = left p ) <-> x = y ) /\
        ( (exists p, f x y = right p) <-> x <> y) . 

Lemma always_correct : forall (f:forall (x y:A), {x = y} + {x <> y}), correct f.
Proof.
    intros f. unfold correct. intros x y. split.
    - split.
        + intros [H _]. exact H.
        + intros H. destruct (f x y) as [H'|H']. 
            { exists H'. reflexivity. }
            { exfalso. apply H'. exact H. }
    - split.
        + intros [H _]. exact H.
        + intros H. destruct (f x y) as [H'|H'].
            { exfalso. apply H. exact H'. }
            { exists H'. reflexivity. }
Qed.
