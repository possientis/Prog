Require Import term.
Require Import var.
Require Import inj_on_list.


Definition injective_on_term (v w:Type) (t:P v) (f:v -> w) : Prop :=
    injective_on_list (Vr t) f.

Arguments injective_on_term {v} {w} _ _.

Lemma injective_on_term_Appl : forall (v w:Type) (t1 t2:P v) (f:v-> w),
    injective_on_term (App t1 t2) f -> injective_on_term t1 f. 
Proof.
    intros v w t1 t2 f H. 
    apply injective_on_list_appl with (Vr t2).
    assumption.
Qed.


Lemma injective_on_term_Appr : forall (v w:Type) (t1 t2:P v) (f:v-> w),
    injective_on_term (App t1 t2) f -> injective_on_term t2 f. 
Proof.
    intros v w t1 t2 f H.
    apply injective_on_list_appr with (Vr t1).
    assumption.
Qed.


Lemma injective_on_term_Lam : forall (v w:Type) (x:v) (t1:P v) (f:v -> w),
    injective_on_term (Lam x t1) f -> injective_on_term t1 f.
Proof.
    intros v w a t1 f H.
    apply injective_on_list_cons with a.
    assumption.
Qed.




