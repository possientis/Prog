Require Import List.


Inductive Perm (a:Type) : list a -> list a -> Prop :=
| pRefl   : forall (xs:list a), Perm a xs xs
| pCons   : forall (x:a)(xs ys:list a), Perm a xs ys -> Perm a (x :: xs) (x :: ys)
| pAppend : forall (x:a)(xs:list a), Perm a (x :: xs) (xs ++ x :: nil)
| pTrans  : forall (xs ys zs:list a), Perm a xs ys -> Perm a ys zs -> Perm a xs zs
.

Ltac perm_aux n :=
    match goal with
    | |- (Perm _ ?l ?l) => apply pRefl
    | |- (Perm _ (?x :: ?l1) (?x :: ?l2)) =>
        let newn := eval compute in (length l1) in
            (apply pCons; perm_aux newn)
    | |- (Perm ?a (?x :: ?l1) ?l2) =>
        match eval compute in n with
        | 1 => fail
        | _ =>
            let l1' := constr:(l1 ++ x :: nil) in
                (apply (pTrans a (x :: l1) l1' l2);
                [ apply pAppend | compute; perm_aux (pred n) ])
        end
    end.

Ltac solve_perm :=
    match goal with
    | |- (Perm _ ?l1 ?l2) =>
        match eval compute in (length l1 = length l2) with
        | (?n = ?n) => perm_aux n
        end
    end.

Lemma L1 : Perm nat (1 :: 2 :: 3 :: nil) (3 :: 2 :: 1 :: nil).
Proof. solve_perm. Qed.


Lemma L2 : Perm nat 
    (0 :: 1 :: 2 :: 3 :: 4 :: 5 :: 6 :: 7 :: 8 :: 9 :: nil)
    (0 :: 2 :: 4 :: 6 :: 8 :: 9 :: 7 :: 5 :: 3 :: 1 :: nil).
Proof. solve_perm. Qed.
    
