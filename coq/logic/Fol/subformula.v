Require Import List.
Require Import Fol.P.

(* Defines the 'list' of sub-formulas of a given formula. We do not have        *)
(* sets here, so using lists instead being understood that the order is         *)
(* irrelevant as are duplicate entries. Hopefully results which are true        *)
(* for sets can be extended for lists as is.                                    *)

Fixpoint Sub (v:Type) (p:P v) : list (P v) :=
    match p with
    | Bot       => cons Bot nil
    | Elem x y  => cons (Elem x y) nil
    | Imp p1 p2 => cons (Imp p1 p2) (Sub v p1 ++ Sub v p2)
    | All x p1  => cons (All x p1) (Sub v p1)
    end.

Arguments Sub {v} _.

(* p is a sub-formula of q if it belongs to the list of sub-formulas of q       *)
Notation "p <= q" := (In p (Sub q)).


Lemma Sub_refl : forall (v:Type) (p:P v), p <= p.
Proof.
    intros v.
    induction p as [|x y|p1 IH1 p2 IH2|x p1 IH1]; simpl; left; reflexivity.
Qed.

(* This lemma will allow us to get transitivity                                 *)
Lemma Sub_incl : forall (v:Type) (p1 p2:P v),
    incl (Sub p1) (Sub p2) <-> p1 <= p2.
Proof.
    intros v p1 p2. split.
    - intros H.  apply H. apply Sub_refl. 
    - revert p1. induction p2 as [|x y|p2 IH2 p2' IH2'|x p1' IH1].
        + simpl. intros p1 [H|H]; intros t.
            { subst. simpl. tauto. }
            { exfalso. assumption. }
        + intros p1 H p H'. simpl in H. destruct H as [H|H]; subst.
            { assumption. }
            { exfalso. assumption. }
        + simpl. intros p1 [H|H]; intros p.
            { subst. simpl. tauto. }
            { intros H'. right. apply in_or_app. 
              apply in_app_or in H. destruct H as [H|H].
                { left.  apply IH2  with p1; assumption. }
                { right. apply IH2' with p1; assumption. }  
            }
        + simpl. intros p1 [H|H]; intros p.
            { subst. simpl. tauto. }
            { intros H'. right. apply IH1 with p1; assumption. }
Qed.

(* transitivity follows from Sub_incl and transitity of incl                    *)
Lemma Sub_tran : forall (v:Type) (p q r: P v),
    p <= q -> q <= r -> p <= r.
Proof.
    intros v p q r Hpq Hqr. apply Sub_incl. 
    apply incl_tran with (Sub q); apply Sub_incl; assumption.
Qed.
