Require Import Eq.
Require Import In.
Require Import Difference.
Require Import Lam.T.
Require Import Lam.Free.

Inductive betaValid_ (v:Type) (e:Eq v) (f:v -> T v) : list v -> T v -> Prop :=
| VVar : forall (xs:list v) (x:v), betaValid_ v _ f xs (Var x)
| VApp : forall (xs:list v) (t1 t2:T v), 
    betaValid_ v _ f xs t1 -> 
    betaValid_ v _ f xs t2 -> 
    betaValid_ v _ f xs (App t1 t2)
| VLam : forall (xs:list v) (x:v) (t1:T v),
    betaValid_ v _ f (cons x xs) t1 ->
    (forall (u:v), u :: Fr (Lam x t1) \\ xs -> ~ x :: Fr (f u)) ->
    betaValid_ v _ f xs (Lam x t1)  
.

Arguments betaValid_ {v} {e}.

Definition betaValid (v:Type) (e:Eq v) (f:v -> T v) (t:T v) : Prop :=
    betaValid_ f nil t.

Arguments betaValid {v} {e}.

Lemma betaValid_var_gen : forall (v:Type) (e:Eq v) (f:v -> T v) (x:v) (xs:list v), 
    betaValid_ f xs (Var x).
Proof.
    intros v e f x xs. constructor.
Qed.

Lemma betaValid_var : forall (v:Type) (e:Eq v) (f:v -> T v) (x:v),
    betaValid f (Var x).
Proof.
    intros v e f x. constructor.
Qed.

Lemma betaValid_app_gen : 
    forall (v:Type) (e:Eq v) (f:v -> T v) (t1 t2:T v) (xs:list v),
    betaValid_ f xs (App t1 t2) 
        <-> 
    betaValid_ f xs t1 /\ betaValid_ f xs t2.
Proof.
    intros v e f t1 t2 xs. split.
    - intros H. remember (App t1 t2) as t eqn:E. destruct H; 
      inversion E. subst. split; assumption.
    - intros [H1 H2]. constructor; assumption.
Qed.

Lemma betaValid_app : forall (v:Type) (e:Eq v) (f:v -> T v) (t1 t2:T v),
    betaValid f (App t1 t2) 
        <-> 
    betaValid f t1 /\ betaValid f t2.
Proof.
    unfold betaValid. intros v e f t1 t2. apply betaValid_app_gen.
Qed.

Lemma betaValid_lam_gen : 
    forall (v:Type) (e:Eq v) (f:v -> T v) (t1:T v) (x:v) (xs:list v),
    betaValid_ f xs (Lam x t1)
        <->
    betaValid_ f (cons x xs) t1 /\
    forall (u:v), u :: Fr (Lam x t1) \\ xs -> ~ x :: Fr (f u).
Proof.
    intros v e f t1 x xs. split.
    - intros H. remember (Lam x t1) as t eqn:E. destruct H;
      inversion E. subst. split; assumption.
    - intros [H1 H2]. constructor; assumption.
Qed.
 
Lemma betaValid_lam : forall (v:Type) (e:Eq v) (f:v -> T v) (t1:T v) (x:v),
    betaValid f (Lam x t1)
        <->
    betaValid_ f (cons x nil) t1 /\
    forall (u:v), u :: Fr (Lam x t1) -> ~ x :: Fr (f u).
Proof.
    unfold betaValid. intros v e f t1 x. 
    rewrite <- (diff_nil v e (Fr (Lam x t1))). apply betaValid_lam_gen.
Qed.
