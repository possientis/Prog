Require Import List.
Import ListNotations.

Require Import Logic.Class.Eq.

Require Import Logic.Func.Composition.

Require Import Logic.List.In.
Require Import Logic.List.Nil.
Require Import Logic.List.Equiv.
Require Import Logic.List.Remove.
Require Import Logic.List.Append.
Require Import Logic.List.Include.
Require Import Logic.List.Coincide.
Require Import Logic.List.Intersect.
Require Import Logic.List.Difference.

Require Import Logic.Lam.Free.
Require Import Logic.Lam.Subst.
Require Import Logic.Lam.Syntax.
Require Import Logic.Lam.Replace.
Require Import Logic.Lam.Variable.

(* Predicate defining the beta-validity of the substitution f for (t,xs).       *)
(* This predicates expresses the fact that when considering the variables of xs *)
(* as bound variables, the substitution f in term t will not give rise to any   *)
(* variable capture, i.e. the substitution is meaningful or 'valid'.            *)
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

(* Predicate defining the beta-validity of the substitution f for term t        *)
Definition betaValid (v:Type) (e:Eq v) (f:v -> T v) (t:T v) : Prop :=
    betaValid_ f nil t.

Arguments betaValid {v} {e}.

(* Substituting in a term 'Var x' never gives rise to variable capture.         *)
(* So any f is always beta-valid for (Var x, xs) for all xs.                    *)
Lemma betaValid_var_gen : forall (v:Type) (e:Eq v) (f:v -> T v) (x:v) (xs:list v), 
    betaValid_ f xs (Var x).
Proof.
    intros v e f x xs. constructor.
Qed.

(* Any f is always beta-valid for Var x.                                        *)
Lemma betaValid_var : forall (v:Type) (e:Eq v) (f:v -> T v) (x:v),
    betaValid f (Var x).
Proof.
    intros v e f x. constructor.
Qed.

(* f is beta-valid for a term (t1 t2) iff it is beta-valid for both t1 and t2.  *)
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

(* f is beta-valid for a term (t1 t2) iff it is beta-valid for both t1 and t2.  *)
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

(* Some monotonicity property of beta-validity.                                 *)
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

(* When a substitution f is beta-valid, free variables are known.               *)
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
                { clear T1 E1 T2 E2 T3 E3 T4 E4 T5 E5. intros ys y H3.
                  destruct H3 as [H3|H3].
                    { subst. rename y into x. intros H3. apply in_map_iff in H3.
                      destruct H3 as [u [H3 H4]]. rewrite <- H3. clear H3.
                      apply H2. simpl. rewrite remove_diff.
                      rewrite <- diff_distrib_app_l'. simpl. assumption. }
                    { inversion H3. }}}
Qed.

Lemma betaValid_free : forall (v:Type) (e:Eq v) (f:v -> T v) (t:T v),
    betaValid f t -> Fr (subst f t) == concat (map (Fr ; f) (Fr t)).
Proof.
    intros v e f t H. rewrite <- (diff_nil v e (Fr t)).
    change (Fr (subst f t) == nil ++ concat (map (Fr; f) (Fr t \\ nil))).
    rewrite <- (inter_nil v e (Fr t)) at 1.
    apply (betaValid_free_gen v e f t nil). assumption.
Qed.


(* When two substitutions coincide, so does their beta-validity.                *)
Lemma betaValid_coincide_gen : 
    forall (v:Type) (e:Eq v) (f g:v -> T v) (t:T v) (xs:list v), 
    coincide (Fr t \\ xs) f g ->
        betaValid_ f xs t <-> betaValid_ g xs t.
Proof.
    intros v e f g. induction t as [x|t1 IH1 t2 IH2|x t1 IH1]; intros xs H.
    - split; intros H1; apply betaValid_var_gen.
    - split; intros H1; apply betaValid_app_gen; 
      rewrite betaValid_app_gen in H1; destruct H1 as [H1 H2];
      simpl in H; rewrite diff_distrib_app_r in H; apply coincide_app' in H;
      destruct H as [H3 H4]; split.
        + apply IH1; assumption.
        + apply IH2; assumption.
        + apply IH1; assumption.
        + apply IH2; assumption.
    - split; intros H1; rewrite betaValid_lam_gen in H1; destruct H1 as [H1 H2];
      apply betaValid_lam_gen; generalize H; intros H';
      simpl in H; rewrite remove_diff in H;
      rewrite <- diff_distrib_app_l' in H; simpl in H;
      split.
        + apply IH1; assumption.
        + intros u H3. assert (f u = g u) as H4.
            { apply H'. assumption. }
          rewrite <- H4. apply H2. assumption.
        + apply IH1; assumption.
        + intros u H3. assert (f u = g u) as H4.
            { apply H'. assumption. }
          rewrite H4. apply H2. assumption.
Qed.

Lemma betaValid_coincide : forall (v:Type) (e:Eq v) (f g:v -> T v) (t:T v), 
    coincide (Fr t) f g ->
        betaValid f t <-> betaValid g t.
Proof.
    intros v e f g t H. unfold betaValid. apply betaValid_coincide_gen. 
    rewrite diff_nil. assumption.
Qed.

Lemma betaValid_subst_gen :
    forall (v:Type) (e:Eq v) (f g:v -> T v) (t:T v) (xs:list v), 
    subst_ f xs t = subst_ g xs t ->
        betaValid_ f xs t <-> betaValid_ g xs t.
Proof.
    intros v e f g t xs H. apply betaValid_coincide_gen.
    apply free_coincide_subst_gen. assumption.
Qed.

Lemma betaValid_subst : forall (v:Type) (e:Eq v) (f g:v -> T v) (t:T v), 
    subst f t = subst g t ->
        betaValid f t <-> betaValid g t.
Proof.
    unfold subst, betaValid. intros v e f g t H. 
    apply betaValid_subst_gen. assumption.
Qed.

(* Beta-validity of f for t on xs and ys are equivalent, provided xs and ys     *)
(* contain the same free variables of t.                                        *)
Lemma betaValid_support : 
    forall (v:Type) (e:Eq v) (f:v -> T v) (t:T v) (xs ys:list v),
    (Fr t /\ xs) == (Fr t /\ ys) ->
        betaValid_ f xs t <-> betaValid_ f ys t.
Proof.
    intros v e f. induction t as [x|t1 IH1 t2 IH2|x t1 IH1]; intros xs ys H.
    - split; intros H1; apply betaValid_var_gen.
    - assert ((Fr t1 /\ xs) == (Fr t1 /\ ys)) as H1.
        { apply inter_sub_equiv with (Fr (App t1 t2)).
            { simpl. apply incl_appl, incl_refl. }
            { assumption. }}
      assert ((Fr t2 /\ xs) == (Fr t2 /\ ys)) as H2.
        { apply inter_sub_equiv with (Fr (App t1 t2)).
            { simpl. apply incl_appr, incl_refl. }
            { assumption. }}
      split; intros H3; apply betaValid_app_gen in H3; destruct H3 as [H3 H4];
      apply betaValid_app_gen; split.
        + apply (IH1 xs ys); assumption.
        + apply (IH2 xs ys); assumption.
        + apply (IH1 xs ys); assumption.
        + apply (IH2 xs ys); assumption.
    - generalize H. intros H'. 
      simpl in H. rewrite remove_diff in H.
      assert ((Fr t1 /\ (cons x xs)) == (Fr t1 /\ (cons x ys))) as H1.
        { change ((Fr t1 /\ (cons x nil ++ xs)) == (Fr t1 /\ (cons x nil ++ ys))).
          remember (Fr t1 /\ (cons x nil ++ xs \\ cons x nil)) as xs' eqn:X.
          remember (Fr t1 /\ (cons x nil ++ ys \\ cons x nil)) as ys' eqn:Y.
          apply (equivCompatLR v xs' ys').
            { rewrite X. apply inter_compat_r, diff_append. }
            { rewrite Y. apply inter_compat_r, diff_append. }
          rewrite X, Y. clear X Y xs' ys'.
          remember ((Fr t1/\cons x nil)++(Fr t1/\(xs \\ cons x nil))) as xs' eqn:X.
          remember ((Fr t1/\cons x nil)++(Fr t1/\(ys \\ cons x nil))) as ys' eqn:Y.
          apply (equivCompatLR v xs' ys').
            { rewrite X. apply inter_distrib_app_l. }
            { rewrite Y. apply inter_distrib_app_l. }
          rewrite X, Y. clear X Y xs' ys'. apply app_compat_r.
          remember ((Fr t1 /\ xs) \\ (cons x nil)) as xs' eqn:X.          
          remember ((Fr t1 /\ ys) \\ (cons x nil)) as ys' eqn:Y.          
          apply (equivCompatLR v xs' ys').
            { rewrite X. apply equivSym, diff_inter_assoc. }
            { rewrite Y. apply equivSym, diff_inter_assoc. }
          rewrite X, Y. clear X Y xs' ys'.
          remember ((Fr t1 \\ (cons x nil)) /\ xs) as xs' eqn:X.
          remember ((Fr t1 \\ (cons x nil)) /\ ys) as ys' eqn:Y.
          apply (equivCompatLR v xs' ys').
            { rewrite X. apply diff_inter_comm. }
            { rewrite Y. apply diff_inter_comm. }
          assumption. }
      assert (Fr (Lam x t1) \\ xs == Fr (Lam x t1) \\ ys) as H6.
            { remember (Fr (Lam x t1) \\ (Fr (Lam x t1) /\ xs)) as xs' eqn:X.
              remember (Fr (Lam x t1) \\ (Fr (Lam x t1) /\ ys)) as ys' eqn:Y.
              apply (equivCompatLR v xs' ys').
                { rewrite X. rewrite diff_inter. apply equivRefl. }
                { rewrite Y. rewrite diff_inter. apply equivRefl. }
              rewrite X, Y. clear X Y xs' ys'. 
              apply diff_compat_r. assumption. }
      destruct H6 as [H6 H7].
      split; intros H3; apply betaValid_lam_gen in H3; destruct H3 as [H3 H4];
      apply betaValid_lam_gen; split.
          + apply (IH1 (cons x xs) (cons x ys)); assumption.
          + intros u H5. apply H4. apply H7. assumption.
          + apply (IH1 (cons x ys) (cons x xs)).
            { apply equivSym. assumption. }
            { assumption. }
          + intros u H5. apply H4. apply H6. assumption.
Qed.

Lemma betaValid_inter_var_gen : 
    forall (v:Type) (e:Eq v) (f:v -> T v) (t:T v) (xs:list v), 
    (var t /\ concat (map (fun u => Fr (f u) \\ [u]) (Fr t \\ xs))) = [] ->
        betaValid_ f xs t.
Proof.
    intros v e f. induction t as [x|t1 IH1 t2 IH2|x t1 IH1]; intros xs H.
    - apply betaValid_var_gen.
    - simpl in H. rewrite diff_distrib_app_r in H. rewrite map_app in H.
      rewrite concat_app in H. rewrite inter_distrib_app_r in H.
      apply app_nil in H. destruct H as [H1 H2].
      apply inter_app_nil_l in H1. destruct H1 as [H1 _].
      apply inter_app_nil_l in H2. destruct H2 as [_ H2].
      apply betaValid_app_gen. split.
        + apply IH1. assumption.
        + apply IH2. assumption.
    - apply betaValid_lam_gen. split.
        + apply IH1. generalize H. intros H'. 
          assert (var t1 <= var (Lam x t1)) as H1.
            { simpl. intros z H1. right. assumption. }
          apply (inter_sub_nil_l v e _ _ _ H1) in H'.
          simpl in H'. rewrite remove_diff in H'.
          rewrite <- diff_distrib_app_l' in H'. simpl in H'. assumption.
        + intros u H1. assert ( Fr (f u) \\ [u] <= 
            concat (map (fun u => Fr (f u) \\ [u]) (Fr (Lam x t1) \\ xs))) as H2. 
            { apply (incl_concat_map v (fun u => Fr (f u) \\ [u])). assumption. }
          apply (inter_sub_nil_r v e _ _ _ H2) in H.
          rewrite nil_charac in H. intros H3. apply (H x).
          apply inter_charac. split.
            { simpl. left. reflexivity. }
            { apply diff_charac. split.
                { assumption. }
                { apply diff_charac in H1. destruct H1 as [H1 H4]. 
                  simpl in H1. rewrite remove_diff in H1. apply diff_charac in H1.
                  destruct H1 as [H1 H5]. intros H6. apply H5. left.
                  destruct H6 as [H6|H6].
                    { subst. reflexivity. }
                    { inversion H6. }}}
Qed.

Lemma betaValid_inter_var : forall (v:Type) (e:Eq v) (f:v -> T v) (t:T v), 
    (var t /\ concat (map (fun u => Fr (f u) \\ [u]) (Fr t))) = [] ->
        betaValid f t.
Proof.
    intros v e f t H. apply betaValid_inter_var_gen. 
    rewrite diff_nil. assumption. 
Qed.


Lemma betaValid_replace_gen : 
    forall (v:Type) (e:Eq v) (s t:T v) (xs:list v) (x:v),
    ~ x :: Fr t \\ xs \/ (var t /\ Fr s) <= [x] -> 
        betaValid_ (s // x) xs t.  
Proof.
    intros v e s t xs x H1. apply betaValid_inter_var_gen.
    apply inter_concat_nil_l. intros u H2. unfold replace.
    destruct (eqDec u x) as [H3|H3].
    - subst. destruct H1 as [H1|H1].
        + exfalso. apply H1. assumption.
        + apply nil_charac. intros u H4. apply inter_charac in H4.
          destruct H4 as [H4 H5]. apply diff_charac in H5.
          destruct H5 as [H5 H6]. apply H6. apply H1. apply inter_charac.
          split; assumption.
    - simpl. destruct (eqDec u u) as [H4|H4]. 
        + apply inter_nil.
        + exfalso. apply H4. reflexivity.
Qed.

Lemma betaValid_replace : forall (v:Type) (e:Eq v) (s t:T v) (x:v),
    ~ x :: Fr t \/ (var t /\ Fr s) <= [x] -> betaValid (s // x) t.  
Proof.
    intros v e s t x H1. apply betaValid_replace_gen. 
    rewrite diff_nil. assumption.
Qed.


Lemma betaValid_compose_lemma :
    forall (v:Type) (e:Eq v) (f g:v -> T v) (xs xs':list v) (x:v) (t1 t:T v),
    t = Lam x t1      ->
    betaValid_ f xs t -> 
        coincide (Fr t \\ xs) (subst_ g xs' ; f) (subst_ g (x :: xs') ; f).
Proof.
    intros v e f g xs xs' x t1 t H1 H2 u H3. unfold comp.
    apply free_subst_intersect_gen, equivSym. 
    rewrite inter_cons_not_in_r.
    - apply equivRefl.
    - rewrite H1 in H2. apply betaValid_lam_gen in H2. destruct H2 as [H2 H4].
      apply H4. rewrite H1 in H3. assumption.
Qed.


Lemma betaValid_compose_subst_gen :
    forall (v:Type) (e:Eq v) (f g:v -> T v) (xs xs':list v) (t:T v),
    xs <= xs'         ->
    betaValid_ f xs t ->
        subst_ (subst_ g xs'; f) xs t = (subst_ g xs' ; subst_ f xs) t.
Proof.
    intros v e f g xs xs' t. revert t xs xs'.
    induction t as [x|t1 IH1 t2 IH2|x t1 IH1]; intros xs xs' H1 H2.
    - unfold comp. simpl. destruct (in_dec eqDec x xs) as [H3|H3].
        + simpl. destruct (in_dec eqDec x xs') as [H4|H4].
            { reflexivity. }
            { exfalso. apply H4, H1. assumption. }
        + reflexivity.
    - apply betaValid_app_gen in H2. destruct H2 as [H2 H3]. simpl.
      rewrite IH1, IH2.
        + reflexivity.
        + assumption.
        + assumption.
        + assumption.
        + assumption.
    - generalize H2. intros H2'. apply betaValid_lam_gen in H2'. 
      destruct H2' as [H3 H4]. simpl.
      assert (Fr (Lam x t1) \\ xs = Fr t1 \\ (x :: xs)) as H5.
        { simpl. rewrite remove_diff. 
          rewrite <- diff_distrib_app_l'. reflexivity. }
      assert (
        subst_ (subst_ g xs'; f) (x :: xs) t1 
        = 
        subst_ (subst_ g (x :: xs'); f) (x :: xs) t1) as H6.
        { apply free_coincide_subst_gen. rewrite <- H5.
          apply betaValid_compose_lemma with t1.
            { reflexivity. }
            { assumption. }}
       rewrite H6, IH1. 
        + reflexivity.
        + apply incl_cons_compat. assumption.
        + assumption.
Qed.

(* Provided the variable substitution f is beta-valid for the term t, then      *)
(* substituting variables in t in one phase according to the map 'subst g ; f'  *)
(* yields the same result as substituting in two phases, first according to f   *)
(* in t, and second according to g in the result of the first substitution.     *)
Lemma betaValid_compose_subst : forall (v:Type) (e:Eq v) (f g:v -> T v) (t:T v),
    betaValid f t -> subst (subst g ; f) t = (subst g ; subst f) t.
Proof.
    intros v e f g t. unfold betaValid, subst. 
    apply betaValid_compose_subst_gen, incl_refl.
Qed.
 
(*
Lemma betaValid_compose_gen :
    forall (v:Type) (e:Eq v) (f g:v -> T v) (xs xs':list v) (t:T v),
        betaValid_ f xs t ->
        betaValid_ g xs' (subst_ f xs t) ->
        betaValid_ (subst_ g xs' ; f) xs t.
Proof.
    intros v e f g xs xs' t. revert t xs xs'. 
    induction t as [x|t1 IH1 t2 IH2|x t1 IH1]; intros xs xs' H1 H2.
    - apply betaValid_var_gen.
    - apply betaValid_app_gen. 
      apply betaValid_app_gen in H1. destruct H1 as [H1 H3].
      simpl in H2. apply betaValid_app_gen in H2. destruct H2 as [H2 H4]. split.
        + apply IH1; assumption.
        + apply IH2; assumption.
    - generalize H1. intros H1'. apply betaValid_lam_gen in H1'.
      destruct H1' as [H6 H7]. simpl in H2. apply betaValid_lam_gen in H2.
      destruct H2 as [H8 H9]. apply betaValid_lam_gen. split.
        + apply (betaValid_coincide_gen v e 
            (subst_ g xs' ; f) (subst_ g (x :: xs') ; f) t1 (x :: xs)).
                { assert (Fr (Lam x t1) \\ xs = Fr t1 \\ (x :: xs)) as H5.
                    { simpl. rewrite remove_diff. 
                      rewrite <- diff_distrib_app_l'. reflexivity. }
                  rewrite <- H5. apply betaValid_compose_lemma with t1.
                    { reflexivity. }
                    { assumption. }}
                { apply IH1; assumption. }
        +

Show.
*)
