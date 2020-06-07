Require Import List.

Require Import Eq.
Require Import In.
Require Import Equiv.
Require Import Remove.
Require Import Append.
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
    intros v e f. induction t as [x|t1 IH1 t2 IH2|x t1 IH1]; intros xs H1; simpl.
    - destruct (in_dec eqDec x xs) as [H2|H2].
        + apply equivRefl.
        + simpl. rewrite app_nil_r. apply equivRefl.
    - apply betaValid_app_gen in H1. destruct H1 as [H1 H2].
    remember (Fr (subst_ f xs t1)) as T1 eqn:E1.    
    remember (Fr (subst_ f xs t2)) as T2 eqn:E2.    
    remember (Fr t1 ++ Fr t2 /\ xs) as T1' eqn:E1'.
    remember (concat (map (Fr ; f) ((Fr t1 ++ Fr t2) \\ xs))) as T2' eqn:E2'.
    remember (Fr t1 /\ xs) as T3 eqn:E3.
    remember (Fr t2 /\ xs) as T4 eqn:E4.
    remember (concat (map (Fr ; f) (Fr t1 \\ xs))) as T5 eqn:E5.
    remember (concat (map (Fr ; f) (Fr t2 \\ xs))) as T6 eqn:E6.
    assert (T1' = T3 ++ T4) as H3. 
        { rewrite E1', E3, E4. apply inter_distrib_app_r. }
    rewrite H3. clear H3 E1' T1'.
    assert (T2' = T5 ++ T6) as H3.
        { rewrite E2', E5, E6. rewrite diff_distrib_app_r, map_app. 
          apply concat_app. }
    rewrite H3. clear H3 E2' T2'.
    rewrite <- app_assoc. rewrite (app_assoc T4).
    apply equivTrans with (T3 ++ (T5 ++ T4) ++ T6).
        + rewrite <- app_assoc. rewrite (app_assoc T3).
          apply app_compat_lr.
            { rewrite E1, E3, E5. apply IH1. assumption. }
            { rewrite E2, E4, E6. apply IH2. assumption. }
        + apply app_compat_r, app_compat_l, app_comm.
    - apply betaValid_lam_gen in H1. destruct H1 as [H1 H2].
      rewrite remove_diff, remove_diff.
      remember (Fr (subst_ f (cons x xs) t1)) as T1 eqn:E1.
      remember (Fr t1 \\ (cons x nil) /\ xs) as T2 eqn:E2.
      remember (concat (map (Fr; f) (Fr t1 \\ (x :: nil) \\ xs))) as T3 eqn:E3.
      remember (Fr t1 /\ (cons x xs)) as T4 eqn:E4.
      remember (concat (map (Fr; f) (Fr t1 \\ (cons x xs)))) as T5 eqn:E5.
      apply equivTrans with ((T4 ++ T5) \\ (cons x nil)).
        + apply diff_compat_l. rewrite E1, E4, E5. apply IH1. assumption.
        + rewrite diff_distrib_app_r. apply app_compat_lr.
            { rewrite E4, E2. split; intros z H6.
                { apply diff_charac in H6. destruct H6 as [H6 H7].
                  apply inter_charac in H6. destruct H6 as [H6 H8].
                  destruct H8 as [H8|H8].
                    { subst. exfalso. apply H7. left. reflexivity. }
                    { apply inter_charac. split.
                        { apply diff_charac. split; assumption. }
                        { assumption. }}}
                { apply inter_charac in H6. destruct H6 as [H6 H7].
                  apply diff_charac in H6. destruct H6 as [H6 H8].
                  apply diff_charac. split.
                    { apply inter_charac. split.
                        { assumption. }
                        { right. assumption. }}
                    { assumption. }}}   
            { rewrite E5, E3. rewrite <- diff_distrib_app_l'. simpl.
              rewrite diff_concat.
                { apply equivRefl. }
                {
Show.
*)
