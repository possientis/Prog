Require Import Le.
Require Import List.

Require Import Leq.
Require Import Max.
Require Import Lam.T.
Require Import Lam.Order.

(* Defines the 'list' of sub-terms of a given term. We do not have sets here,   *)
(* so using lists instead, being understood that the order is irrelevant as     *) 
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
Notation "t <<= s" := (In t (Sub s)) (at level 50).
   
(* Being a 'sub-term of' is reflexive relation                                  *)
Lemma Sub_refl : forall (v:Type) (t:T v), t <<= t.
Proof.
    intros v.
    induction t as [x|t1 IH1 t2 IH2|x t1 IH1]; simpl; left; reflexivity.
Qed.

(* This lemma will allow us to get transitivity                                 *)
Lemma Sub_incl : forall (v:Type) (t1 t2:T v),
    incl (Sub t1) (Sub t2) <-> t1 <<= t2.
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

(* Transitivity follows from Lemma Sub_incl and transitity of incl              *)
Lemma Sub_tran : forall (v:Type) (r s t:T v),
    r <<= s -> s <<= t -> r <<= t.
Proof.
    intros v r s t Hrs Hst. apply Sub_incl. 
    apply incl_tran with (Sub s); apply Sub_incl; assumption.
Qed.


(* This lemma will allow us to get anti-symmetry                                *) 
Lemma ord_monotone : forall (v:Type) (t1 t2:T v),
    t1 <<= t2  -> ord t1 <= ord t2.
Proof. 
    intros v t1 t2. revert t1. 
    induction t2 as [x|t2 IH2 t2' IH2'|x t1' IH1];
    simpl; intros t1 [H|H].
    - subst. apply le_n.
    - exfalso. assumption.
    - subst. apply le_n.
    - apply in_app_or in H. destruct H as [H|H].
        { apply le_trans with (ord t2).
            { apply IH2. assumption. }
            { apply le_S. apply n_le_max. }}
        { apply le_trans with (ord t2').
            { apply IH2'. assumption. }
            { apply le_S. apply m_le_max. }}
    - subst. apply le_n.
    - apply le_S, IH1. assumption.
Qed.

(* Anti-symmentry follows from Lemma ord_monotone                               *)
Lemma Sub_anti : forall (v:Type) (t1 t2:T v),
    t1 <<= t2 -> t2 <<= t1 -> t1 = t2.
Proof.
    intros v t1 t2. revert t1. 
    induction t2 as [x|t2 IH2 t2' IH2'|x t1' IH1]; 
    simpl; intros t1 [H|H].
    - subst. tauto.
    - exfalso. assumption.
    - subst. tauto.
    - intros H'. exfalso. apply in_app_or in H. destruct H as [H|H];
      apply ord_monotone in H; apply ord_monotone in H'; 
      simpl in H'; apply not_le_Sn_n with (ord t1).
        { apply le_trans with (S (ord t2)).
            { apply le_n_S. assumption. }
            { apply le_trans with (S (max (ord t2) (ord t2'))).
                { apply le_n_S. apply n_le_max. }
                { assumption. }
            }
        }
        { apply le_trans with (S (ord t2')).
            { apply le_n_S. assumption. }
            { apply le_trans with (S (max (ord t2) (ord t2'))).
                { apply le_n_S. apply m_le_max. }
                { assumption. }
            }
        }
    - subst. tauto. 
    - intros H'. exfalso.
      apply ord_monotone in H. apply ord_monotone in H'.
      simpl in H'. apply not_le_Sn_n with (ord t1).
      apply le_trans with (S (ord t1')).
        { apply le_n_S. assumption. }
        { assumption. }
Qed.

(* A set theoretic formulation of the same result is Sub (f t) = f (Sub t)      *)
(* with the customary abuse of notations, whereby 'f t' denotes the function    *)
(* f acting on the term t (formally fmap f t), Sub (f t) is simply the function *)
(* Sub applied to the term (f t), and 'f (Sub t)' denotes the direct image of   *)
(* the set (Sub t) (a list for us) by function f acting on terms (so fmap f).   *) 
(* The direct image is expressed by 'map'. In heuristic terms, the following    *)
(* lemma expresses the fact that sub-terms of 'fmap f t' are the images of the  *)
(* sub-terms of t by (fmap f).                                                  *)

(* We could have a point-free version of this lemma                             *)
Lemma Sub_fmap : forall (v w:Type) (f:v -> w) (t:T v),
    Sub (fmap f t) = map (fmap f) (Sub t).
Proof.
    intros v w f.
    induction t as [x|t1 IH1 t2 IH2|x t1 IH1]; simpl.
    - reflexivity.
    - rewrite IH1, IH2, map_app. reflexivity.
    - rewrite IH1. reflexivity.
Qed.



