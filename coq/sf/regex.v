Require Import bool.
Require Import nat.
Require Import le.
Require Import list.
Require Import In.
Require Import fold.


Inductive regex (a:Type) : Type :=
| EmptySet  : regex a
| EmptyStr  : regex a
| Char      : a -> regex a
| App       : regex a -> regex a -> regex a
| Union     : regex a -> regex a -> regex a
| Star      : regex a -> regex a
.

Arguments EmptySet  {a}.
Arguments EmptyStr  {a}.
Arguments Char      {a} _.
Arguments App       {a} _ _.
Arguments Union     {a} _ _.
Arguments Star      {a} _.


Inductive exp_match (a:Type) : list a -> regex a -> Prop :=
| MEmpty    :   exp_match a [] EmptyStr
| MChar     :   forall (c:a), exp_match a [c] (Char c)
| MApp      :   forall (s1 s2:list a) (r1 r2:regex a),  
                exp_match a s1 r1 -> 
                exp_match a s2 r2 -> 
                exp_match a (s1 ++ s2) (App r1 r2) 
| MUnionL   :   forall (s:list a) (r1 r2:regex a),
                exp_match a s r1 -> 
                exp_match a s (Union r1 r2)
| MUnionR   :   forall (s:list a) (r1 r2:regex a),
                exp_match a s r2 -> 
                exp_match a s (Union r1 r2)
| MStar0    :   forall (r:regex a), exp_match a [] (Star r)
| MStarApp  :   forall (s1 s2:list a) (r:regex a),
                exp_match a s1 r -> 
                exp_match a s2 (Star r) -> 
                exp_match a (s1 ++ s2) (Star r)
.

Arguments exp_match {a} _ _.
Arguments MEmpty {a}.
Arguments MChar {a} _.
Arguments MApp {a} _ _ _ _ _ _.
Arguments MUnionL {a} _ _ _ _.
Arguments MUnionR {a} _ _ _ _.
Arguments MStar0 {a} _.
Arguments MStarApp {a} _ _ _ _ _.

Notation "s =~ r" := (exp_match s r) (at level 80).

Example regex_ex1 : [1] =~ Char 1.
Proof. apply MChar. Qed.

Example regex_ex2 : [1,2] =~ App (Char 1) (Char 2).
Proof. 
    apply (MApp [1] [2]).
    - apply MChar.
    - apply MChar.
Qed.
    
Example regex_ex3 : ~([1,2] =~ Char 1).
Proof. intros H. inversion H. Qed.

Fixpoint regex_of_list (a:Type) (l:list a) : regex a :=
    match l with
    | []        => EmptyStr
    | (x :: xs) => App (Char x) (regex_of_list a xs)
    end.

Arguments regex_of_list {a} _.

Example regex_ex4 : [1,2,3] =~ regex_of_list [1,2,3].
Proof. 
    apply (MApp [1]). 
    - apply MChar.
    - apply (MApp [2]).
        + apply MChar.
        + apply (MApp [3]).
            { apply MChar. }
            { apply MEmpty. }
Qed.

Lemma MStar1 : forall (a:Type) (s:list a) (r:regex a),
    s =~ r -> s =~ (Star r).
Proof.
    intros a s r H. rewrite <- (app_nil_r _ s). apply MStarApp. 
    - exact H.
    - apply MStar0.
Qed.

Lemma empty_is_empty : forall (a:Type) (s:list a), ~(s =~ EmptySet).
Proof. intros a s H. inversion H. Qed.

Lemma MUnion : forall (a:Type) (s:list a) (r1 r2:regex a),
    s =~ r1 \/ s =~ r2 -> s =~ Union r1 r2.
Proof.
    intros a s r1 r2 [H|H].
    - apply MUnionL. exact H.
    - apply MUnionR. exact H.
Qed.

Lemma regex_of_list_correct : forall (a:Type) (s1 s2:list a),
    s1 =~ regex_of_list s2 <-> s1 = s2.
Proof.
    intros a s1 s2. split. 
    - revert s1. induction s2 as [|x xs H]. 
        + intros s H'. inversion H'. reflexivity.
        + intros s H'. inversion H'. 
            apply H in H4. rewrite H4. inversion H3. reflexivity.
    - intros H. rewrite H. clear H. clear s1. revert s2. intros s.
        induction s as [|x xs H].
            + apply MEmpty.
            + assert ([x]++xs = x::xs) as H0. { reflexivity. }
                rewrite <- H0. apply MApp.
                    { apply MChar. }
                    { fold (regex_of_list xs). exact H. }
Qed.


Fixpoint regex_chars (a:Type) (r:regex a) : list a :=
    match r with
    | EmptySet      => []
    | EmptyStr      => []
    | Char x        => [x]
    | App r1 r2     => regex_chars a r1 ++ regex_chars a r2
    | Union r1 r2   => regex_chars a r1 ++ regex_chars a r2
    | Star r1       => regex_chars a r1
    end.

Arguments regex_chars {a} _.


Theorem in_regex_match : forall (a:Type) (s:list a) (r:regex a) (x:a),
    s =~ r -> In x s -> In x (regex_chars r).
Proof.
    intros a s r x H. induction H as 
        [    
        |c
        |s1 s2 r1 r2 H1 IH1 H2 IH2
        |s1 r1 r2 H1 IH1
        |s2 r1 r2 H2 IH2
        |r1
        |s1 s2 r1 H1 IH1 H2 IH2
        ]
        . 
    - intros H. inversion H.
    - intros [H|H]. 
        + rewrite H. simpl. left. reflexivity.
        + inversion H.
    - rewrite In_app_iff. intros [H|H].
        + simpl. rewrite In_app_iff. left. apply IH1. exact H.
        + simpl. rewrite In_app_iff. right. apply IH2. exact H.
    - intros H. simpl. rewrite In_app_iff. left. apply IH1. exact H.
    - intros H. simpl. rewrite In_app_iff. right. apply IH2. exact H.
    - intros H. inversion H.
    - rewrite In_app_iff. intros [H|H].
        + apply IH1. exact H.
        + apply IH2. exact H. 
Qed.


Fixpoint regex_not_empty (a:Type) (r:regex a) : bool :=
    match r with
    | EmptySet      => false
    | EmptyStr      => true
    | Char x        => true
    | App r1 r2     => regex_not_empty a r1 && regex_not_empty a r2 
    | Union r1 r2   => regex_not_empty a r1 || regex_not_empty a r2 
    | Star r1       => true
    end.

Arguments regex_not_empty {a} _.

Lemma regex_not_empty_correct : forall (a:Type) (r:regex a),
    (exists s, s =~ r) <-> regex_not_empty r = true.
Proof.
    intros a r. split.
    - intros [s H]. induction H as 
        [    
        |c
        |s1 s2 r1 r2 H1 IH1 H2 IH2
        |s1 r1 r2 H1 IH1
        |s2 r1 r2 H2 IH2
        |r1
        |s1 s2 r1 H1 IH1 H2 IH2
        ]
        . 
        + reflexivity.
        + reflexivity.
        + simpl. rewrite IH1, IH2. reflexivity.
        + simpl. rewrite IH1. reflexivity. 
        + simpl. rewrite IH2. rewrite orb_comm. reflexivity.
        + reflexivity.
        + reflexivity.
    - induction r as [| |c|r1 IH1 r2 IH2|r1 IH1 r2 IH2|r1 IH]. 
        + intros H. inversion H.
        + intros. exists []. apply MEmpty.
        + intros. exists [c]. apply MChar.
        + intros H. simpl in H. rewrite andb_true_iff in H. destruct H as [H1 H2].
            apply IH1 in H1. apply IH2 in H2.
            destruct H1 as [s1 H1]. destruct H2 as [s2 H2].
            exists (s1 ++ s2). apply MApp. { exact H1. } { exact H2. }
        + intros H. simpl in H. rewrite orb_true_iff in H. destruct H as [H1|H2].
            { apply IH1 in H1. destruct H1 as [s1 H1]. exists s1.
                apply MUnionL. exact H1. }
            { apply IH2 in H2. destruct H2 as [s2 H2]. exists s2.
                apply MUnionR. exact H2. }
        + intros. exists []. apply MStar0.
Qed.


Lemma star_app : forall (a:Type) (s1 s2:list a) (r:regex a),
    s1 =~ Star r -> s2 =~ Star r -> s1 ++ s2 =~ Star r.
Proof.
    intros a s1 s2 r H1. remember (Star r) as r' eqn:H'.
    revert s2 H'. revert r. induction H1 as
        [   
        | c
        | s1 s2 r1 r2 H1 IH1 H2 IH2
        | s1 r1 r2 H1 IH1
        | s1 r1 r2 H2 IH2
        | r1
        | s1 s2 r1 H1 IH1 H2 IH2
        ]
        .
    - intros r s2 H. inversion H.
    - intros r s2 H. inversion H.
    - intros r s3 H. inversion H. 
    - intros r s2 H. inversion H.
    - intros r s2 H. inversion H.
    - intros r s2 H H'. exact H'.
    - intros r s3 H H'. rewrite <- app_assoc. apply MStarApp.
        + exact H1.
        + apply (IH2 r). 
            { exact H. }
            { exact H'. }
Qed.

Lemma MStar' : forall (a:Type) (xss:list (list a)) (r:regex a),
    (forall xs, In xs xss -> xs =~ r) -> foldr app [] xss =~ Star r.
Proof.
    intros a xss. induction xss as [|xs xss H].
    - intros r H'. apply MStar0.
    - intros r H'. apply MStarApp.
        + apply H'. left. reflexivity.
        + fold (foldr app [] xss). apply H. intros ys H0. apply H'.
            right. exact H0.
Qed.


Lemma MStar'' : forall (a:Type) (s:list a) (r:regex a),
    s =~ Star r -> exists xss:list (list a), 
        s = foldr app [] xss /\ forall xs, In xs xss -> xs =~ r.
Proof.
    intros a s r H. remember (Star r) as r' eqn:H'. revert r H'. 
    induction H as
        [   
        | c
        | s1 s2 r1 r2 H1 IH1 H2 IH2
        | s1 r1 r2 H1 IH1
        | s1 r1 r2 H2 IH2
        | r1
        | s1 s2 r1 H1 IH1 H2 IH2
        ]
        .
    - intros r H. inversion H.
    - intros r H. inversion H.
    - intros r H. inversion H.
    - intros r H. inversion H.
    - intros r H. inversion H.
    - intros r H. exists []. split.
        + reflexivity.
        + intros xs H'. inversion H'.
    - intros r H. inversion H as [H3]. apply (IH2 r) in H. clear IH2 IH1.
        destruct H as [xss H]. exists (s1 :: xss). destruct H as [H4 H5]. split.
        + simpl. rewrite H4. reflexivity.
        + intros xs. intros [H6|H6].
            { rewrite <- H6, <- H3. exact H1. }
            { apply H5. exact H6. }
Qed.        


Fixpoint pumpN (a:Type) (r:regex a) : nat :=
    match r with
    | EmptySet      => 0
    | EmptyStr      => 1
    | Char _        => 2
    | App r1 r2     => pumpN a r1 + pumpN a r2
    | Union r1 r2   => pumpN a r1 + pumpN a r2
    | Star _        => 1
    end.

Arguments pumpN {a} _.

Fixpoint napp (a:Type) (n:nat) (l:list a) : list a :=
    match n with
    | 0     => []
    | S p   => l ++ napp a p l
    end.

Arguments napp {a} _ _.


Lemma Star_napp : forall (a:Type) (s:list a) (r:regex a),
    s =~ r -> forall (n:nat), napp n s =~ Star r.
Proof.
    intros a s r H n. induction n as [|n IH].
    - simpl. apply MStar0.
    - simpl. apply MStarApp.
        + exact H.
        + exact IH.
Qed.


Lemma pumping : forall (a:Type) (r:regex a) (s:list a),
    s =~ r -> 
    pumpN r <= length s -> 
    exists (s1 s2 s3:list a), 
        s = s1 ++ s2 ++ s3                          /\ 
        s2 <> []                                    /\
        forall (m:nat), s1 ++ napp m s2 ++ s3 =~ r  .
Proof.
    intros a r s H.
    induction H as
        [   
        | c
        | s1 s2 r1 r2 H1 IH1 H2 IH2
        | s1 r1 r2 H1 IH1
        | s1 r1 r2 H2 IH2
        | r1
        | s1 s2 r1 H1 IH1 H2 IH2
        ]
        .
    - intros H'. inversion H'.
    - intros H'. inversion H' as [|m p H1 H2]. inversion H1.
    - simpl. intros H'. rewrite app_length in H'.
        apply sum_leq_sum in H' as [H3|H3].
        + apply IH1 in H3 as [s3 [s4 [s5 [H4 [H5 H6]]]]]. clear IH1 IH2.
        exists s3. exists s4. exists (s5 ++ s2). split.
        { rewrite H4. rewrite <- app_assoc, <- app_assoc. reflexivity. }
        { split. 
            { exact H5. }
            { intros m. rewrite app_assoc, app_assoc. apply MApp.
                { rewrite <- app_assoc. apply H6. }
                { exact H2. }
            }
        }
        + apply IH2 in H3 as [s3 [s4 [s5 [H4 [H5 H6]]]]]. clear IH1 IH2.
            exists (s1 ++ s3). exists s4. exists s5. split.
            { rewrite H4. rewrite <- app_assoc. reflexivity. }
            { split.
                { exact H5. }
                { intros m.  rewrite <- app_assoc. apply MApp.
                    { exact H1. }
                    { apply H6. }
                }
            }
    - simpl. intros H'. assert (pumpN r1 <= length s1) as H3.
        { apply le_trans with (m:= pumpN r1 + pumpN r2).
            {  apply le_plus_l. }
            { exact H'. } 
        }
                
        apply IH1 in H3 as [s3 [s4 [s5 [H4 [H5 H6]]]]]. clear IH1.
        exists s3. exists s4. exists s5. split.
        { exact H4. }
        { split.
            { exact H5. }
            { intros m. apply MUnionL. apply H6. }
        }
    - simpl. intros H'. rewrite plus_comm in H'. 
        assert (pumpN r2 <= length s1) as H3.
        { apply le_trans with (m:= pumpN r2 + pumpN r1).
            { apply le_plus_l. }
            { exact H'. } 
        }
        apply IH2 in H3 as [s3 [s4 [s5 [H4 [H5 H6]]]]]. clear IH2.
        exists s3. exists s4. exists s5. split.
        { exact H4. }
        { split.
            { exact H5. }
            { intros m. apply MUnionR. apply H6. }
        }
    - intros H'. inversion H'.
    - simpl. intros H'. simpl in IH2. rewrite app_length in H'. 
        destruct (length s2) eqn:H3.
        + exists []. exists s1. exists []. split.
            { rewrite length_0_iff_nil in H3. rewrite H3. reflexivity. }
            { split.
                { intros H. rewrite <- length_0_iff_nil in H. rewrite H in H'.
                    inversion H'. }
                { intros m. simpl. rewrite app_nil_r. apply Star_napp. exact H1. }
            }
        + assert (1 <= S n) as H. { apply n_le_m__Sn_le_Sm, le_0_n. }
            apply IH2 in H as [s3 [s4 [s5 [H4 [H5 H6]]]]]. clear IH2 IH1.
                exists (s1 ++ s3). exists s4. exists s5. split.
                    { rewrite <- app_assoc, H4. reflexivity. }
                    { split.
                        { exact H5. }
                        { intros m. rewrite <- app_assoc. apply MStarApp.
                            { exact H1. }
                            { apply H6. }
                        }
                     }
Qed.
