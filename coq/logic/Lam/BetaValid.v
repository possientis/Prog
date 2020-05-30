Require Import List.

Require Import Eq.
Require Import In.
Require Import Equiv.
Require Import Include.
Require Import Intersect.
Require Import Difference.
Require Import Composition.
Require Import Lam.T.
Require Import Lam.Free.
Require Import Lam.Subst.

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

Lemma betaValid_incl : 
    forall (v:Type) (e:Eq v) (f:v -> T v) (t:T v) (xs ys:list v),
        xs <= ys -> betaValid_ f xs t -> betaValid_ f ys t.
Proof.
    intros v e f. induction t as [x|t1 IH1 t2 IH2|x t1 IH1]; intros xs ys H1 H2.
    - apply betaValid_var_gen.
    - apply betaValid_app_gen. apply betaValid_app_gen in H2. 
      destruct H2 as [H2 H3]. split.
        + apply IH1 with xs; assumption.
        + apply IH2 with xs; assumption.
    - apply betaValid_lam_gen. apply betaValid_lam_gen in H2. 
      destruct H2 as [H2 H3]. split.
        + apply IH1 with (cons x xs).
            { intros z [H4|H4].
                { subst. left. reflexivity. }
                { right. apply H1. assumption. }}
            { assumption. }
        + intros u H4. apply (diff_incl_r v e xs ys) in H4.
            { apply H3. assumption. }
            { assumption. }
Qed.

(*
Lemma betaValid_free_gen : 
    forall (v:Type) (e:Eq v) (f:v -> T v) (t:T v) (xs:list v),
    betaValid_ f xs t ->
    Fr (subst_ f xs t) == (Fr t /\ xs) ++ concat (map (Fr ; f) (Fr t \\ xs)).
Proof.
    intros v e f. induction t as [x|t1 IH1 t2 IH2|x t1 IH1]; intros xs H1.
    - simpl. destruct (in_dec eqDec x xs) as [H2|H2].
        + apply equivRefl.
        + simpl. rewrite app_nil_r. apply equivRefl.
    - simpl. apply betaValid_app_gen in H1. destruct H1 as [H1 H2].
Show.
*)
