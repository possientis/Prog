Require Import List.

Definition char := nat.
Definition string := list char.

(* regular expressions defined as an inductive type *)
Inductive Exp : Set :=
  | Lit : char -> Exp
  | And : Exp -> Exp -> Exp
  | Or  : Exp -> Exp -> Exp
  | Many: Exp -> Exp.

(* each regular expression has an associated 'language', namely a set of 
strings which are 'recognized' by the regular expression. Normally, this set 
of strings can easily be defined recursively. However, it is not finite in 
general. Here we are attempting to define this set of strings as a type
'Language r'. So we are defining a family of types (indexed by a regular 
expression) with an inductive definition. Now given a regular expression
r:Exp, the type 'Language r' is not quite a set of strings. It is more like
an inductive type, i.e. some free algebra of some sort. However, any element
of type Language r can easily be translated into a string via some
'semantics' function defined below *)

Inductive Language : Exp -> Set := 
  | LangLit     : forall c:char, Language (Lit c)
  | LangAnd     : forall r1 r2: Exp, 
                    Language r1  -> Language r2  -> Language (And r1 r2)
  | LangOrLeft  : forall r1 r2: Exp, Language r1  -> Language (Or r1 r2)
  | LangOrRight : forall r1 r2: Exp, Language r2  -> Language (Or r1 r2)
  | LangEmpty   : forall r: Exp, Language (Many r)
  | LangMany    : forall r: Exp, 
                    Language (Many r) -> Language r -> Language (Many r).

Fixpoint semantics {r:Exp}(s:Language r) : string :=
  match s with
    | LangLit c           => (c::nil)
    | LangAnd r1 r2 s1 s2 => semantics s1 ++ semantics s2
    | LangOrLeft r1 r2 s  => semantics s
    | LangOrRight r1 r2 s => semantics s
    | LangEmpty r         => nil
    | LangMany r s1 s2    => semantics s1 ++ semantics s2
  end.

(* We now attempt to formalize the relation 'recognize' which expresses the 
fact that a string is an element of the language defined by a regular expression. 
Since we have already formalized the notion of 'Language', the fact that s:string 
is 'recognized' by a regular expression r (i.e. that it belongs to its language), 
can be expressed as the fact that s = semantics x for some x:Language r. Rather 
than proceeding this way, we now attempt to define the 'recognize' relation 
directly as an inductive predicate. We shall then attempt to prove the equivalence 
between the two approaches. *)

Inductive recognize : Exp -> string -> Prop :=
  | recogLit    : forall c:char, recognize (Lit c) (c::nil)
  | recogAnd    : forall (r1 r2:Exp)(s1 s2:string), 
      recognize r1 s1 -> recognize r2 s2 -> recognize (And r1 r2) (s1 ++ s2)
  | recogOrLeft : forall (r1 r2:Exp)(s :string), 
      recognize r1 s -> recognize (Or r1 r2) s
  | recogOrRight: forall (r1 r2:Exp)(s :string), 
      recognize r2 s -> recognize (Or r1 r2) s
  | recogEmpty  : forall (r:Exp), recognize (Many r) nil
  | recogMany   : forall (r:Exp) (s1 s2: string), 
      recognize (Many r) s1 -> recognize r s2 -> recognize (Many r) (s1 ++ s2).

(* First we show that a recognized string is part of the language *)
(* The proof flows naturally from an induction on the inductive predicate *)
Lemma recognize_imp_in_language: forall (r:Exp)(s:string),
  recognize r s -> (exists x:Language r, semantics x = s).
Proof.
  (* induction on the recognize predicate *)
  intros r s H. generalize H. elim H.

  clear H r s. intros c H. exists (LangLit c). simpl. reflexivity.

  clear H r s. intros r1 r2 s1 s2 H1 H1' H2 H2' H.
  elim H1'. intros x1 S1. clear H1'. 
  elim H2'. intros x2 S2. clear H2'.
  exists (LangAnd r1 r2 x1 x2). simpl. rewrite S1, S2. reflexivity.
  exact H2. exact H1.

  clear H r s. intros r1 r2 s H H' H0. clear H0.
  elim H'. intros x S. exists (LangOrLeft r1 r2 x). simpl. exact S. exact H.

  clear H r s. intros r1 r2 s H H' H0. clear H0.
  elim H'. intros x S. exists (LangOrRight r1 r2 x). simpl. exact S. exact H.

  clear H r s. intros r H. exists (LangEmpty r). simpl. reflexivity. 

  clear H r s. intros r s1 s2 H1 H1' H2 H2' H.
  elim H1'. intros x1 S1. clear H1'. 
  elim H2'. intros x2 S2. clear H2'.
  exists (LangMany r x1 x2). simpl. rewrite S1, S2. reflexivity.
  exact H2. exact H1.
Qed.

(* Next we show that all strings of the language are recognized *)
(* very simple coq proof with an induction on x                 *)
Lemma recognize_language: forall (r:Exp)(x: Language r),
  recognize r (semantics x).
Proof.
  (* induction on x *)
  intros r x. elim x. 
  (* x = LangLit c *)
  clear r x. simpl. apply recogLit.
  (* x = LangAnd r1 r2 x1 x2 *)
  clear r x. intros r1 r2 x1 H1 x2 H2. simpl. 
  apply recogAnd. exact H1. exact H2. 
  (* x = LangOrLeft r1 r2 x1 *)
  clear r x. intros r1 r2 x1 H1. simpl.
  apply recogOrLeft. exact H1.
  (* x = LangOrRight r1 r2 x2 *)
  clear r x. intros r1 r2 x2 H2. simpl.
  apply recogOrRight. exact H2.
  (* x = LangEmpty r *)
  clear r x. intros r. simpl. apply recogEmpty.
  (* x = LangMany r x1 x2 *)
  clear r x. intros r x1 H1 x2 H2. simpl.
  apply recogMany. exact H1. exact H2.
Qed.
 

(* re-formatting previous lemma *)
Lemma in_language_imp_recognize: forall (r:Exp)(s:string),
  (exists x:Language r, semantics x = s) -> recognize r s. 
Proof.
  intros r s H. elim H. intros x Hx. clear H. rewrite <- Hx.
  apply recognize_language.
Qed.


(* This efectively show the equivalence between the two approaches *)
Lemma in_language_is_recognize: forall (r:Exp)(s:string),
  (exists x:Language r, semantics x = s) <-> recognize r s.
Proof.
  intros r s. split. apply in_language_imp_recognize.
  apply recognize_imp_in_language.
Qed.

(* At this stage, we have defined what a regular expression is as well
as what it means for a string to be recognized by a regular expression.
Now an obvious question arises: given a regular expression (r:Exp) and 
a string (s:string), how do I decide whether s is recognized by r? 
From a mathematical point of view, there exists a function 
f : Exp -> string -> bool which returns 1 if and only if s belongs to 
the language of r (i.e. s = semantics x for some x:Language r)
However, we would like a program which implements such a function *)







(*
(* this definition is needed for the next lemma *)
Definition Lang_of_Lit_Pred {r:Exp}(x:Language r) := (* major trick *)
  match r (* return Language r -> Prop *) with
   | Lit c => fun x => x = LangLit c
   | other => fun _ => True
 end x.
 
Lemma Lang_of_Lit: forall (c:char)(x:Language (Lit c)),
  x = LangLit c.
Proof.
  intros c x. fold (Lang_of_Lit_Pred x).
  cut(forall (r:Exp)(x:Language r), Lang_of_Lit_Pred x). eauto.
  clear c x. intros r x. destruct x; simpl; auto.
Qed.

(* this definition is needed for the next lemma *)
Definition Lang_of_And_Pred {r:Exp}(x:Language r) := (* major trick *)
  match r with
    | And r1 r2   => fun x => 
        exists (x1: Language r1)(x2: Language r2), x = LangAnd r1 r2 x1 x2
    | other       => fun _ => 
        True
  end x.

Lemma Lang_of_And: forall (r1 r2: Exp)(x: Language (And r1 r2)),
  exists (x1: Language r1)(x2: Language r2), 
  x = LangAnd r1 r2 x1 x2.
Proof. 
  intros r1 r2 x. fold (Lang_of_And_Pred x).
  cut(forall (r:Exp)(x:Language r), Lang_of_And_Pred x). eauto.
  clear r1 r2 x. intros r x. destruct x; simpl; eauto.
Qed.

(* this definition is needed for the next lemma *)
Definition Lang_of_Or_Pred {r:Exp}(x:Language r) := (* major trick *)
  match r with
    | Or r1 r2   => fun x => 
        (exists (x1: Language r1), x = LangOrLeft r1 r2 x1) \/
        (exists (x2: Language r2), x = LangOrRight r1 r2 x2)
    | other       => fun _ => 
        True
  end x.

Lemma Lang_of_Or: forall (r1 r2: Exp)(x: Language (Or r1 r2)),
  (exists (x1: Language r1), x = LangOrLeft r1 r2 x1) \/
  (exists (x2: Language r2), x = LangOrRight r1 r2 x2).
Proof.
  intros r1 r2 x. fold (Lang_of_Or_Pred x). 
  cut(forall (r:Exp)(x:Language r), Lang_of_Or_Pred x). eauto.
  clear r1 r2 x. intros r x. destruct x; simpl; eauto.
Qed.



(* this definition is needed for the next lemma *)
Definition Lang_of_Many_Pred {r:Exp}(x:Language r) := (* major trick *)
  match r with
    | Many r'     => fun x => 
        (x = LangEmpty r') \/
        (exists (x1: Language (Many r'))(x2: Language r'), 
          x = LangMany r' x1 x2)
    | other       => fun _ => 
        True
  end x.


Lemma Lang_of_Many: forall (r: Exp)(x: Language (Many r)),
  (x = LangEmpty r) \/
  (exists (x1: Language (Many r))(x2: Language r),
    x = LangMany r x1 x2).
Proof. 
  intros r x. fold (Lang_of_Many_Pred x).
  cut (forall (r: Exp)(x:Language r), Lang_of_Many_Pred x). eauto.
  clear r x. intros r x. destruct x; simpl; eauto.
Qed.

*)  
