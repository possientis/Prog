Require Import List.
Require Import Lam.T.

(* Defines the 'list' of sub-terms of a given term. We do not have sets here,   *)
(* so using lists instead being understood that the order is irrelevant as      *) 
(* are duplicate entries. Hopefully results which are true for sets can be      *)
(* extended for lists as is.                                                    *)

Fixpoint Sub (v:Type) (t:T v) : list (T v) :=
    match t with
    | Var x     => cons (Var x) nil
    | App t1 t2 => cons (App t1 t2) (Sub v t1 ++ Sub v t2) 
    | Lam x t1  => cons (Lam x t1) (Sub v t1)
    end.

Arguments Sub {v} _.

(* t is a sub-term of s if it belongs to the list of sub-terms of s             *)
Notation "t <= s" := (In t (Sub s)).
   
(* Being a 'sub-term of' is reflexive relation                                  *)
Lemma Sub_refl : forall (v:Type) (t:T v), t <= t.
Proof.
    intros v.
    induction t as [x|t1 IH1 t2 IH2|x t1 IH1]; simpl; left; reflexivity.
Qed.

(* This lemma will allow us to get transitivity                                 *)
Lemma Sub_incl : forall (v:Type) (t1 t2:T v),
    incl (Sub t1) (Sub t2) <-> t1 <= t2.
Proof.
    intros v t1 t2. split.
    - intros H.  apply H. apply Sub_refl. 
    - revert t1. induction t2 as [x|t2 IH2 t2' IH2'|x t1' IH1].
        + intros t1 H t H'. simpl in H. destruct H as [H|H]; subst.
            { assumption. }
            { exfalso. assumption. }
        + simpl. intros t1 [H|H]; intros t.
            { subst. simpl. tauto. }
            { intros H'. right. apply in_or_app. 
              apply in_app_or in H. destruct H as [H|H].
                { left.  apply IH2  with t1; assumption. }
                { right. apply IH2' with t1; assumption. }  
            }
        + simpl. intros t1 [H|H]; intros t.
            { subst. simpl. tauto. }
            { intros H'. right. apply IH1 with t1; assumption. }
Qed.

(* transitivity follows from Sub_incl and transitity of incl                    *)
Lemma Sub_tran : forall (v:Type) (r s t: T v),
    r <= s -> s <= t -> r <= t.
Proof.
    intros v r s t Hrs Hst. apply Sub_incl. 
    apply incl_tran with (Sub s); apply Sub_incl; assumption.
Qed.
