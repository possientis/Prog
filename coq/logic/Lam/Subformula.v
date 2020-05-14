Require Import Le.
Require Import List.

Require Import In.
Require Import Eq.
Require Import Leq.
Require Import MinMax.
Require Import Include.

Require Import Lam.T.
Require Import Lam.Order.
Require Import Lam.Bound.
Require Import Lam.Variable.

(* Defines the 'list' of sub-terms of a given term. We do not have sets here,   *)
(* so using lists instead, being understood that the order is irrelevant as     *) 
(* are duplicate entries. Hopefully results which are true for sets can be      *)
(* extended for lists as is.                                                    *)

Fixpoint Sub (v:Type) (t:T v) : list (T v) :=
    match t with
    | Var x     => cons (Var x) nil
    | App t1 t2 => cons (App t1 t2) (Sub v t1 ++ Sub v t2) 
    | Lam x t1  => cons (Lam x t1)  (Sub v t1)
    end.

Arguments Sub {v} _.

(* s is a sub-term of t if it belongs to the list of sub-terms of t             *)
Notation "s <<= t" := (s :: Sub t) (at level 50).
   
(* Being a 'sub-term of' is reflexive relation                                  *)
Lemma Sub_refl : forall (v:Type) (t:T v), t <<= t.
Proof.
    intros v.
    induction t as [x|t1 IH1 t2 IH2|x t1 IH1]; simpl; left; reflexivity.
Qed.

(* This lemma will allow us to get transitivity                                 *)
Lemma Sub_incl : forall (v:Type) (t1 t2:T v),
    Sub t1 <= Sub t2 <-> t1 <<= t2.
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

Open Scope nat_scope.

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


(* We defined (s <<= t) in Haskell as a function:                               *)
(* (<<=) :: (Eq v) => T v -> T v -> Bool                                        *)
(* Hence we expect that (s <<= t) is a decidable propostion in coq, provided    *)
(* the type v has decidable equality.                                           *)
Lemma SubDecidable : forall (v:Type) (e:Eq v),
   forall (s t:T v), {s <<= t} + {~ s <<= t}.
Proof.
    intros v e s t. revert s. revert t. 
    induction t as [x|t1 IH1 t2 IH2|x t1 IH1].
    - destruct s as [y|s1 s2|y s1].
        + destruct (eqDec x y) as [E|E].
            { subst. left. apply Sub_refl. }
            { right. intros H. apply E. destruct H as [H|H].
                { inversion H. reflexivity. }
                { inversion H. }
            }
        + right. intros H. destruct H as [H|H]; inversion H.
        + right. intros H. destruct H as [H|H]; inversion H.
    - intros s.  destruct (eqDec s (App t1 t2)) as [E|E].
        + subst. left. apply Sub_refl.
        + destruct (IH1 s) as [E1|E1], (IH2 s) as [E2|E2].
            { left. right. apply in_or_app. left.  assumption. }
            { left. right. apply in_or_app. left.  assumption. }
            { left. right. apply in_or_app. right. assumption. }
            { right. intros H. destruct H as [H|H]. 
                { subst. apply E. reflexivity. }
                { apply in_app_or in H. destruct H as [H|H].
                    { apply E1. assumption. }
                    { apply E2. assumption. }
                }
            }
    - intros s. destruct (eqDec s (Lam x t1)) as [E|E].
        + subst. left. apply Sub_refl.
        + destruct (IH1 s) as [E1|E1].
            { left. right. assumption. }
            { right. intros H. destruct H as [H|H].
                { subst. apply E. reflexivity. }
                { apply E1. assumption. }
            }
Qed.

Open Scope Include_scope.

Lemma Sub_var : forall (v:Type) (s t:T v), s <<= t -> var s <= var t.
Proof.
    intros v s t. revert t s. 
    induction t as [x|t1 IH1 t2 IH2|x t1 IH1]; intros s [H|H].
    - subst. apply incl_refl.
    - inversion H.
    - subst. apply incl_refl.
    - apply in_app_or in H. destruct H as [H|H].
        + apply incl_tran with (var t1).
            { apply IH1. assumption. }
            { apply incl_appl, incl_refl. }
        + apply incl_tran with (var t2).
            { apply IH2. assumption. }
            { apply incl_appr, incl_refl. }
    - subst. apply incl_refl.
    - apply incl_tl, IH1. assumption. 
Qed.

Lemma Sub_bnd : forall (v:Type) (s t:T v), s <<= t -> bnd s <= bnd t.
Proof.
    intros v s t. revert t s. 
    induction t as [x|t1 IH1 t2 IH2|x t1 IH1]; intros s [H|H].
    - subst. apply incl_refl.
    - inversion H.
    - subst. apply incl_refl.
    - apply in_app_or in H. destruct H as [H|H].
        + apply incl_tran with (bnd t1).
            { apply IH1. assumption. }
            { apply incl_appl, incl_refl. }
        + apply incl_tran with (bnd t2).
            { apply IH2. assumption. }
            { apply incl_appr, incl_refl. }
    - subst. apply incl_refl.
    - apply incl_tl, IH1. assumption. 
Qed.
