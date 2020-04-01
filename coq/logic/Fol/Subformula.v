Require Import Le.
Require Import List.

Require Import In.
Require Import Eq.
Require Import Leq.
Require Import Max.
Require Import Include.
Require Import Fol.P.
Require Import Fol.Order.
Require Import Fol.Bound.
Require Import Fol.Variable.


(* Defines the 'list' of sub-formulas of a given formula. We do not have        *)
(* sets here, so using lists instead, being understood that the order is        *)
(* irrelevant as are duplicate entries. Hopefully results which are true        *)
(* for sets can be extended for lists as is.                                    *)

Fixpoint Sub (v:Type) (p:P v) : list (P v) :=
    match p with
    | Bot       => cons Bot nil
    | Elem x y  => cons (Elem x y) nil
    | Imp p1 p2 => cons (Imp p1 p2) (Sub v p1 ++ Sub v p2)
    | All x p1  => cons (All x p1)  (Sub v p1)
    end.

Arguments Sub {v} _.

Definition isSubFormulaOf (v:Type) (p q:P v) : Prop := p :: Sub q.
Arguments isSubFormulaOf {v} _ _.

(* p is a sub-formula of q if it belongs to the list of sub-formulas of q       *)
Notation "p <<= q" := (isSubFormulaOf p q) (at level 50).
 
Lemma Sub_refl : forall (v:Type) (p:P v), p <<= p.
Proof.
    intros v.
    induction p as [|x y|p1 IH1 p2 IH2|x p1 IH1]; simpl; left; reflexivity.
Qed.

(* This lemma will allow us to get transitivity                                 *)
Lemma Sub_incl : forall (v:Type) (p1 p2:P v),
    Sub p1 <= Sub p2 <-> p1 <<= p2.
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


Open Scope nat_scope.   (* <= now interpreted as inequality between nats        *)

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

Open Scope Include_scope.


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


(* We defined (p <<= q) in Haskell as a function:                               *)
(* (<<=) :: (Eq v) => P v -> P v -> Bool                                        *)
(* Hence we expect that (p <<= q) is a decidable propostion in coq, provided    *)
(* the type v has decidable equality.                                           *)
Lemma SubDecidable : forall (v:Type) (e:Eq v),
   forall (p q:P v), {p <<= q} + {~ p <<= q}.
Proof.
    intros v e p q. revert p. revert q.
    induction q as [|x y|q1 IH1 q2 IH2|x q1 IH1].
    - destruct p as [|x' y'|p1 p2|x' p1].
        + left. apply Sub_refl.
        + right. intros H. destruct H as [H|H]; inversion H.
        + right. intros H. destruct H as [H|H]; inversion H.
        + right. intros H. destruct H as [H|H]; inversion H.
    - destruct p as [|x' y'|p1 p2|x' p1].
        + right. intros H. destruct H as [H|H]; inversion H.
        + destruct (eqDec x x') as [Ex|Ex], (eqDec y y') as [Ey|Ey].
            { subst. left. apply Sub_refl. }
            { right. intros H. destruct H as [H|H]; inversion H.
              subst. apply Ey. reflexivity.
            }
            { right. intros H. destruct H as [H|H]; inversion H.
              inversion H. subst. apply Ex. reflexivity.
            }
            { right. intros H. destruct H as [H|H]; inversion H.
              inversion H. subst. apply Ex. reflexivity.
            }
        + right. intros H. destruct H as [H|H]; inversion H.
        + right. intros H. destruct H as [H|H]; inversion H.
    - intros p. destruct (eqDec p (Imp q1 q2)) as [E|E].
        + subst. left. apply Sub_refl.
        + destruct (IH1 p) as [E1|E1], (IH2 p) as [E2|E2].
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
    - intros p. destruct (eqDec p (All x q1)) as [E|E].
        + subst. left. apply Sub_refl.
        + destruct (IH1 p) as [E1|E1].
            { left. right. assumption. }
            { right. intros H. destruct H as [H|H].
                { subst. apply E. reflexivity. }
                { apply E1. assumption. }
            }
Qed.



Lemma Sub_var : forall (v:Type) (p q:P v),
    p <<= q -> var p <= var q.
Proof.
    intros v p q. revert q p. 
    induction q as [|x y|p1 IH1 p2 IH2|x p1 IH1]; intros p [H|H].
    - subst. apply incl_refl.
    - inversion H.
    - subst. apply incl_refl.
    - inversion H.
    - subst. apply incl_refl. 
    - apply in_app_or in H. destruct H as [H|H].
        + apply incl_tran with (var p1).
            { apply IH1. assumption. }
            { apply incl_appl, incl_refl. }
        + apply incl_tran with (var p2).
            { apply IH2. assumption. }
            { apply incl_appr, incl_refl. }
    - subst. apply incl_refl.
    - apply incl_tl, IH1. assumption. 
Qed.


Lemma Sub_bnd : forall (v:Type) (p q:P v),
    p <<= q -> bnd p <= bnd q.
Proof.
    intros v p q. revert q p. 
    induction q as [|x y|q1 IH1 q2 IH2|x q1 IH1]; intros p [H|H].
    - subst. apply incl_refl.
    - inversion H.
    - subst. apply incl_refl.
    - inversion H.
    - subst. apply incl_refl.
    - apply in_app_or in H. destruct H as [H|H].
        + apply incl_tran with (bnd q1).
            { apply IH1. assumption. }
            { apply incl_appl, incl_refl. }
        + apply incl_tran with (bnd q2).
            { apply IH2. assumption. }
            { apply incl_appr, incl_refl. }
    - subst. apply incl_refl.
    - apply incl_tl, IH1. assumption. 
Qed.
