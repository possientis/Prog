Require Import list.
Require Import fold.
Require Import In.

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



