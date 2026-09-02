Require Import List.
Import ListNotations.

Parameter M:Set.
Parameter e:M.
Parameter f:M -> M -> M.
Infix "+" := f.

Parameter assoc : forall a b c, (a + b) + c = a + (b + c).
Parameter identl: forall a, e + a = a.
Parameter identr: forall a, a + e = a.

(* This is about proof by reflection                                            *)
(* We have some domain type 'M', and need to prove equalities between           *)
(* expressions in that domain. We first define a type to reify such expressions *)
Inductive MExp : Set :=
| Ident : MExp
| Var   : M -> MExp (* things that are not '+' or 'e', most likely variables    *)
| Op    : MExp -> MExp -> MExp
.

(* We are able to define some semantics on that expression type                 *) 
Fixpoint mDenote (me:MExp) : M :=
    match me with
    | Ident         => e
    | Var v         => v
    | Op me1 me2    => mDenote me1 + mDenote me2
    end.
(* However, we crucially have some notion of 'normal' form on that expression   *)
(* type, representing any expression as a list of values in M                   *)
Fixpoint flatten (me : MExp) : list M :=
    match me with
    | Ident         => nil
    | Var x         => x :: nil
    | Op me1 me2    => flatten me1 ++ flatten me2
    end.

(* Any list of values in M can be assigned a value in M                         *)
Fixpoint mlDenote (ms:list M) : M :=
    match ms with
    | nil       => e
    | x :: ms   => x + mlDenote ms
    end.    

(* Needed for correctness lemma                                                 *)
Lemma appDenote : forall (xs ys:list M), 
    mlDenote xs + mlDenote ys = mlDenote (xs ++ ys).
Proof.
    induction xs as [|x xs IH]; intros ys.
    - simpl. rewrite identl. reflexivity.
    - simpl. rewrite assoc. rewrite IH. reflexivity.
Qed.

(* evaluating the expression is the same as evaluating the 'normal' form        *)
Lemma flattenCorrect : forall (me:MExp), mDenote me = mlDenote (flatten me).
Proof.
    induction me as [|m|e1 IH1 e2 IH2].
    - reflexivity.
    - simpl. rewrite identr. reflexivity.
    - simpl. rewrite <- appDenote. rewrite IH1, IH2. reflexivity.
Qed.

(* So in order to prove that two expressions evaluates to the same value in M   *)
(* It is sufficient to prove that their 'normal' forms have same value.         *)
Theorem monoidReflect : forall (me1 me2:MExp),
    mlDenote (flatten me1) = mlDenote (flatten me2) -> 
    mDenote me1 = mDenote me2.
Proof.
    intros me1 me2 H. rewrite flattenCorrect, flattenCorrect. assumption.
Qed.

(* We cannot write a function reify : M -> MExp because we cannot pattern match *)
(* on elements of M. However, we can write a tactic which *does* pattern match  *)
(* on elements of M and returns a corresponding value in MExp                   *)
Ltac reify me :=
    match me with
    | e     => Ident
    | ?me1 + ?me2   =>
        let r1 := reify me1 in
        let r2 := reify me2 in
            constr:(Op r1 r2)
    | _ => constr:(Var me)
    end.

(* 'change' tactic changes the goal into something equivalent                   *)
Lemma L1 : 2 * 2 = 4.
Proof.
    change (2 * 2 = 2 * 2).
    change (4 = 4).
    reflexivity.
Qed.

(* This is the key tactic. We pattern match the current goal for a case when    *)
(* attempting to prove equality between two expressions in M. We then reify     *)
(* each expression and obtain corresponding values r1 r2 of our expression type *)
(* MExp. Of course the semantics of r1 is me1 and the semantics of r2 is me2    *)
(* which was the whole point of reification. Hence we can change the goal to be *)
(* proven from 'me1 = me2' to 'mDenote r1 = mDenote r2'. We then apply the      *)
(* theorem monoidReflect to convert that goal into:                             *)
(*      'mlDenote (flatten r1) = mlDenote (flatten r2)'                         *)
(* We finally invoke the 'simpl' tactic to re-expressed that goal in terms of   *)
(* an equality between two terms of M. So we started by having to prove an      *)
(* equality between two terms of M, and end up with having to prove yet another *)
(* equality between two terms of M. Why have we benefitted from all this? The   *)
(* benefit is that due to the reduction to 'normal' form, you stand a very good *)
(* chance that the final goal to be proven will be equality between two         *)
(* identical terms, which can simply be dispatched with 'reflexivity'.          *)
Ltac monoid :=
    match goal with
    | [ |- ?me1 = ?me2 ]    =>
        let r1 := reify me1 in
        let r2 := reify me2 in
            change (mDenote r1 = mDenote r2);
                apply monoidReflect; simpl
    end.

Theorem T1 : forall (a b c d:M), a + b + c + d = a + (b + c) + d.
Proof.
    intros a b c d. monoid. reflexivity.
Qed.

Theorem T2 : forall (a b c d:M), a + b + c + d = a + (b + (c + d)).
Proof.
    intros a b c d. monoid. reflexivity.
Qed.

Theorem T3 : forall (a b c d:M), a + b + c + d = a + ((b + c) + d).
Proof.
    intros a b c d. monoid. reflexivity.
Qed.

(*
Print T1.
*)
