Require Import Le.
Require Import List.

Require Import le.
Require Import max.
Require Import Fol.P.
Require Import Fol.order.

(* Defines the 'list' of sub-formulas of a given formula. We do not have        *)
(* sets here, so using lists instead, being understood that the order is        *)
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
Notation "p <<= q" := (In p (Sub q)) (at level 50).


Lemma Sub_refl : forall (v:Type) (p:P v), p <<= p.
Proof.
    intros v.
    induction p as [|x y|p1 IH1 p2 IH2|x p1 IH1]; simpl; left; reflexivity.
Qed.

(* This lemma will allow us to get transitivity                                 *)
Lemma Sub_incl : forall (v:Type) (p1 p2:P v),
    incl (Sub p1) (Sub p2) <-> p1 <<= p2.
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
Lemma Sub_tran : forall (v:Type) (p q r:P v),
    p <<= q -> q <<= r -> p <<= r.
Proof.
    intros v p q r Hpq Hqr. apply Sub_incl. 
    apply incl_tran with (Sub q); apply Sub_incl; assumption.
Qed.


(* This lemma will allow us to get anti-symmetry                                *) 
Lemma ord_monotone : forall (v:Type) (p1 p2:P v),
    p1 <<= p2  -> ord p1 <= ord p2.
Proof. 
    intros v p1 p2. revert p1. 
    induction p2 as [|x y|p2 IH2 p2' IH2'|x p1' IH1];
    simpl; intros p1 [H|H].
    - subst. apply le_n.
    - exfalso. assumption.
    - subst. apply le_n.
    - exfalso. assumption.
    - subst. apply le_n.
    - apply in_app_or in H. destruct H as [H|H].
        { apply le_trans with (ord p2).
            { apply IH2. assumption. }
            { apply le_S. apply n_le_max. }}
        { apply le_trans with (ord p2').
            { apply IH2'. assumption. }
            { apply le_S. apply m_le_max. }}
    - subst. apply le_n.
    - apply le_S, IH1. assumption.
Qed.


(* Anti-symmentry follows from Lemma ord_monotone                               *)
Lemma Sub_anti : forall (v:Type) (p1 p2:P v),
    p1 <<= p2 -> p2 <<= p1 -> p1 = p2.
Proof.
    intros v p1 p2. revert p1. 
    induction p2 as [|x y|p2 IH2 p2' IH2'|x p1' IH1];
    simpl; intros p1 [H|H].
    - subst. tauto.
    - exfalso. assumption.
    - subst. tauto.
    - exfalso. assumption.
    - subst. tauto.
    - intros H'. exfalso. apply in_app_or in H. destruct H as [H|H];
      apply ord_monotone in H; apply ord_monotone in H'; 
      simpl in H'; apply not_le_Sn_n with (ord p1).
        { apply le_trans with (S (ord p2)).
            { apply le_n_S. assumption. }
            { apply le_trans with (S (max (ord p2) (ord p2'))).
                { apply le_n_S. apply n_le_max. }
                { assumption. }
            }
        }
        { apply le_trans with (S (ord p2')).
            { apply le_n_S. assumption. }
            { apply le_trans with (S (max (ord p2) (ord p2'))).
                { apply le_n_S. apply m_le_max. }
                { assumption. }
            }
        }
    - subst. tauto. 
    - intros H'. exfalso.
      apply ord_monotone in H. apply ord_monotone in H'.
      simpl in H'. apply not_le_Sn_n with (ord p1).
      apply le_trans with (S (ord p1')).
        { apply le_n_S. assumption. }
        { assumption. } 
Qed.


(* A set theoretic formulation of the same result is Sub (f p) = f (Sub p)      *)
(* with the customary abuse of notations, whereby 'f p' denotes the function    *)
(* f acting on the formula p (formally fmap f p), Sub (f p) is simply the       *)
(* function Sub applied to the formula (f p), and 'f (Sub p)' denotes the       *)
(* direct image of the set (Sub p) (a list for us) by function f acting on      *)
(* formulas (so fmap f). The direct image is expressed by 'map'. In heuristic   *)
(* terms, the following lemma expresses the fact that sub-formulas of the       *)
(* formula 'fmap f p' are the images of the sub-formulas of p by (fmap f).      *)

(* We could have a point-free version of this lemma                             *)
Lemma Sub_fmap : forall (v w:Type) (f:v -> w) (p:P v),
    Sub (fmap f p) = map (fmap f) (Sub p).
Proof.
    intros v w f.
    induction p as [|x y|p1 IH1 p2 IH2|x p1 IH1]; simpl.
    - reflexivity.
    - reflexivity.
    - rewrite IH1, IH2, map_app. reflexivity.
    - rewrite IH1. reflexivity.
Qed.
