Require Import List.
Import ListNotations.

Variable M:Set.
Variable e:M.
Variable f:M -> M -> M.
Infix "+" := f.

Hypothesis assoc : forall a b c, (a + b) + c = a + (b + c).
Hypothesis identl: forall a, e + a = a.
Hypothesis identr: forall a, a + e = a.

Inductive MExp : Set :=
| Ident : MExp
| Var   : M -> MExp (* catch-all for things we can't understand *)
| Op    : MExp -> MExp -> MExp
.

Fixpoint mDenote (me:MExp) : M :=
    match me with
    | Ident         => e
    | Var v         => v
    | Op me1 me2    => mDenote me1 + mDenote me2
    end.

Fixpoint mlDenote (ms:list M) : M :=
    match ms with
    | nil       => e
    | x :: ms   => x + mlDenote ms
    end.    

Fixpoint flatten (me : MExp) : list M :=
    match me with
    | Ident         => nil
    | Var x         => x :: nil
    | Op me1 me2    => flatten me1 ++ flatten me2
    end.

Lemma appDenote : forall (xs ys:list M), 
    mlDenote xs + mlDenote ys = mlDenote (xs ++ ys).
Proof.
    induction xs as [|x xs IH]; intros ys.
    - simpl. rewrite identl. reflexivity.
    - simpl. rewrite assoc. rewrite IH. reflexivity.
Qed.

Lemma flattenCorrect : forall (me:MExp), mDenote me = mlDenote (flatten me).
Proof.
    induction me as [|m|e1 IH1 e2 IH2].
    - reflexivity.
    - simpl. rewrite identr. reflexivity.
    - simpl. rewrite <- appDenote. rewrite IH1, IH2. reflexivity.
Qed.
