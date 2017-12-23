Require Import list.

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
| MApp      :   forall (r1 r2:regex a) (s1 s2:list a), 
                exp_match a s1 r1 -> 
                exp_match a s2 r2 -> 
                exp_match a (s1 ++ s2) (App r1 r2) 
| MUnionL   :   forall (r1 r2:regex a) (s:list a),
                exp_match a s r1 -> 
                exp_match a s (Union r1 r2)
| MUnionR   :   forall (r1 r2:regex a) (s:list a),
                exp_match a s r2 -> 
                exp_match a s (Union r1 r2)
| MStar0    :   forall (r:regex a), exp_match a [] (Star r)
| MStarApp  :   forall (r:regex a) (s1 s2:list a),
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
    apply (MApp _ _ [1] [2]).
    - apply MChar.
    - apply MChar.
Qed.
    

