Require Import Lt.
Require Import Le.
Require Import Peano_dec.


Definition LEM   : Prop := forall (A:Prop), A \/ ~A.
Definition IRREL : Prop := forall (A:Prop) (p q:A), p = q.

(* Definition works for 'strict-like' relations                                 *)
Inductive Accessible (a:Type)(r:a -> a -> Prop) : a -> Prop := 
| MkAcc : forall (x:a), (forall (y:a), r y x -> Accessible a r y) -> 
    Accessible a r x
.

Arguments Accessible {a}.

Definition WellFounded (a:Type) (r:a -> a -> Prop) :=
    forall (x:a), Accessible r x.

Arguments WellFounded {a}.

Lemma lt_is_acc : forall (a:Type) (r:a -> a -> Prop) (x y:a),
    r x y -> Accessible r y  -> Accessible r x.
Proof.
    intros a r x y R Ay. destruct Ay as [y H].
    apply H. assumption.
Qed.

Lemma nat_is_acc : forall (n:nat), Accessible lt n.
Proof.
    induction n as [|n IH]; constructor.
    - intros n H. inversion H.
    - intros m H. destruct (eq_nat_dec m n) as [H'|H'].
        + subst. assumption.
        + unfold lt in H. apply le_S_n in H. 
          apply le_lt_or_eq in H. destruct H as [H|H].
            { apply lt_is_acc with n; assumption. }
            { apply H' in H. contradiction. }
Qed.

Lemma lt_is_wf : WellFounded lt.
Proof.
    unfold WellFounded. intros n. apply nat_is_acc.
Qed.

Definition Reflexive (a:Type) (r:a -> a -> Prop) : Prop :=
    forall (x:a), r x x.

Definition AntiSym (a:Type) (r:a -> a -> Prop) : Prop := 
    forall (x y:a), r x y -> r y x -> x = y.

Definition Transitive (a:Type) (r:a -> a -> Prop) : Prop :=
    forall (x y z:a), r x y -> r y z -> r x z.

Definition Total (a:Type) (r:a -> a -> Prop) : Prop :=
    forall (x y:a), r x y \/ r y x.

Arguments Reflexive {a}.
Arguments AntiSym {a}.
Arguments Transitive {a}.
Arguments Total {a}.

Definition TotalOrder (a:Type) (r:a -> a -> Prop) : Prop :=
    Reflexive r /\ AntiSym r /\ Transitive r /\ Total r.

Arguments TotalOrder {a}.

Definition Minimal (a:Type) (r:a -> a -> Prop) (x:a) : Prop :=
    forall (y:a), r y x -> x = y.

Arguments Minimal {a}.

(* There is an injection j:b -> a, i.e. b is a subset of a                      *)
Inductive Embedding (b a:Type) : Type :=
| Embed : forall (j:b -> a), (forall (x y:b), j x = j y -> x = y) -> Embedding b a
.

Arguments Embed {b} {a}.

(* Restricting relation r on a to subset b                                      *)
Definition restrict (a b:Type) (r:a -> a -> Prop) (e:Embedding b a)(x y:b) 
    : Prop :=
        match e with
        | Embed j _ => r (j x) (j y)
        end.

Arguments restrict {a} {b}.

(* Every non-empty subset has a minimal element                                 *)
Definition HasMinProp (a:Type) (r:a -> a -> Prop) : Prop :=
    forall (b:Type) (e:Embedding b a), forall (y:b), exists (z:b), 
    Minimal (restrict r e) z.

Arguments HasMinProp {a}.

Definition WellOrder (a:Type) (r:a -> a -> Prop) : Prop :=
    TotalOrder r /\ HasMinProp r.

Arguments WellOrder {a}.

(* returns a 'strict' counterpart of a given relation                           *)
Definition strict (a:Type) (r:a -> a -> Prop) (x y:a) : Prop :=
    r x y /\ x <> y.

Arguments strict {a}.

Lemma LeReflexive : Reflexive le.
Proof.
    unfold Reflexive. apply le_refl.
Qed.

Lemma LeAntiSym : AntiSym le.
Proof.
    unfold AntiSym. apply le_antisym.
Qed.

Lemma LeTransitive : Transitive le.
Proof.
    unfold Transitive. apply le_trans.
Qed.

Lemma LeTotal : Total le.
Proof.
    unfold Total. intros n m.
    destruct (eq_nat_dec n m) as [H|H].
    - subst. left. apply le_n.
    - apply nat_total_order in H. destruct H as [H|H].
        + left. apply le_trans with (S n).
            { apply le_S, le_n. }
            { assumption. }
        + right. apply le_trans with (S m).
            { apply le_S, le_n. }
            { assumption. }
Qed.


Lemma LeTotalOrder : TotalOrder le.
Proof.
    unfold TotalOrder. split.
    - apply LeReflexive.
    - split.
        + apply LeAntiSym.
        + split.
            { apply LeTransitive. }
            { apply LeTotal. }
Qed.


Lemma LeHasMinProp : LEM -> HasMinProp le.
Proof.
    unfold HasMinProp. intros L b e x. destruct e as [j p].
    unfold Minimal. unfold restrict. remember (j x) as n eqn:E.
    assert (j x <= n) as H. { rewrite E. apply le_n. } clear E.
    revert H. revert p. revert x. revert j. revert b.
    induction n as [|n IH]; intros b j x p H.
    - exists x. intros y H'. apply p. inversion H.
      rewrite H1 in H'. inversion H'. rewrite H1, H2. reflexivity.
    - apply le_lt_or_eq in H. destruct H as [H|H]. 
        + unfold lt in H. apply le_S_n in H. apply IH with x; assumption.
        + destruct (L (exists (y:b), j y <= n)) as [H'|H'].
            { clear H. clear x. destruct H' as [x H]. 
              apply IH with x; assumption. }
            { exists x. intros y H0. rewrite H in H0. apply le_lt_or_eq in H0.
              destruct H0 as [H0|H0]. 
                { unfold lt in H0. apply le_S_n in H0. exfalso.
                  apply H'. exists y. assumption. }
                { apply p. rewrite H, H0. reflexivity. }}
Qed.

(* It seems surprising we needed LEM to prove this. However, defining a well    *)
(* order relies on the notion of embedding from any type b to nat.              *)
Lemma LeWellOrder : LEM -> WellOrder le.
Proof.
    intros L. unfold WellOrder. split.
    - apply LeTotalOrder.
    - apply LeHasMinProp. assumption.
Qed.


Definition NotAccessibleType (a:Type) (r:a -> a -> Prop) : Type := 
    { x : a | ~Accessible r x }.

Arguments NotAccessibleType {a}.

Definition NotAccessibleInj (a:Type) (r:a -> a -> Prop) 
    : NotAccessibleType r -> a := @proj1_sig _ _.

Arguments NotAccessibleInj {a}.

Lemma NotAccessibleInjInj :
    forall (a:Type) (I:IRREL)(r:a -> a -> Prop),
    forall (x y:NotAccessibleType r), 
        NotAccessibleInj r x = NotAccessibleInj r y  -> x = y.
Proof. 
    intros a I r x y H. destruct x as [x p]. destruct y as [y q].
    unfold NotAccessibleInj in H. simpl in H. revert p q.
    rewrite H. intros p q. assert (p = q) as E. { apply I. } 
    rewrite E. reflexivity.
Qed.

Arguments NotAccessibleInjInj {a}.

Definition NotAccessibleEmbedding (a:Type) (I:IRREL)(r:a -> a -> Prop)
    : Embedding (NotAccessibleType r) a := Embed
        (NotAccessibleInj r)
        (NotAccessibleInjInj I r).

Arguments NotAccessibleEmbedding {a}.

Lemma WellOrderAllAccessible : forall (a:Type) (r:a -> a -> Prop),
    LEM         -> 
    IRREL       ->
    WellOrder r ->
    forall (x:a), Accessible (strict r) x.
Proof.
    intros a r L I [[H1 [H2 [H3 H4]]] H5] x. 
    destruct (L (Accessible (strict r) x)) as [H|H].
    - assumption.
    - unfold HasMinProp in H5.
      remember (NotAccessibleType (strict r)) as b eqn:Eb.
      unfold NotAccessibleType in Eb. 
      remember (NotAccessibleEmbedding I (strict r)) as e eqn:Ee.
      unfold NotAccessibleType in e.
      remember (@exist a (fun x => ~Accessible (strict r) x) x H) as x' eqn:Ex. 
      remember (H5 b) as H6 eqn:E. clear E. rewrite Eb in H6. clear H5.
      remember (H6 e x') as H7 eqn:E. clear E. clear H6. clear Ex. clear x'.
      clear H. exfalso. clear x. clear Eb. clear b. destruct H7 as [x H].
      destruct x as [x p]. unfold Minimal in H. unfold restrict in H.
      unfold NotAccessibleEmbedding in Ee. rewrite Ee in H.
      unfold NotAccessibleInj in H. simpl in H. apply p. constructor.
      intros y Hy. destruct (L (Accessible (strict r) y)) as [H'|H'].
        + assumption.
        + remember 
            (@exist a (fun x => ~Accessible (strict r) x) y H') as y' eqn:Ey.  
          remember (H y') as H5 eqn:E. clear E. rewrite Ey in H5. simpl in H5. 
          clear H. unfold strict in Hy. destruct Hy as [H6 H7]. clear Ee. 
          clear e. remember (H5 H6) as H8 eqn:E. clear E. clear H5. clear Ey. 
          clear y'. clear H6.  exfalso. apply H7. inversion H8. reflexivity.
Qed.

(* If r is a well-order, then (strict r) is well-founded                        *)
Theorem WellOrderWF : forall (a:Type) (r:a -> a -> Prop),
    LEM         ->
    IRREL       ->
    WellOrder r -> 
    WellFounded (strict r).
Proof.
    intros a r L I H. unfold WellFounded. apply WellOrderAllAccessible; 
    assumption.
Qed.

(* Acc is defined by Coq.                                                       *)
Lemma Acc_Accessible : forall (a:Type) (r:a -> a -> Prop) (x:a),
    Accessible r x <-> Acc r x.
Proof.
    intros a r x. split; intros H; induction H as [x H IH]; 
    constructor; assumption.
Qed.

(* well_founded is defined by Coq.                                              *)
Lemma well_founded_WellFounded : forall (a:Type) (r:a -> a -> Prop),
    WellFounded r <-> well_founded r.
Proof.
    intros a r. split; intros H.
    - unfold well_founded. intros x. rewrite <- Acc_Accessible. apply H.
    - unfold WellFounded.  intros x. rewrite Acc_Accessible.    apply H.
Qed.

Check Acc_inv.

(* Do it with 'refine' first ...                                                *)
Definition AccessibleInv' : forall (a:Type) (r:a -> a -> Prop) (x:a),
    Accessible r x -> forall (y:a), r y x -> Accessible r y.
Proof. refine (
    fun (a:Type) =>
        fun (r:a -> a -> Prop) =>
            fun (x:a) =>
                fun (p:Accessible r x) =>
                    match p with
                    | MkAcc _ _ _ q => q
                    end
).
Defined.

(* Of course, this can be done the usual way ...                                *)                             
Definition AccessibleInv3 : forall (a:Type) (r:a -> a -> Prop) (x:a),
    Accessible r x -> forall (y:a), r y x -> Accessible r y.
Proof.
    intros a r x H. destruct H. assumption.
Qed.


Definition AccessibleInv : forall (a:Type) (r:a -> a -> Prop) (x:a),
    Accessible r x -> forall (y:a), r y x -> Accessible r y :=
    fun (a:Type) =>
        fun (r:a -> a -> Prop) =>
            fun (x:a) =>
                fun (p:Accessible r x) =>
                    match p with
                    | MkAcc _ _ _ q => q
                    end.


Check Fix_F.
Print Fix_F.

(* Do it with 'refine' first: Attempting to redefine Fix_F                      *)
Definition WFRecursion_F': forall (a:Type) (r:a -> a -> Prop) (c:a -> Type),
    (forall (x:a), (forall (y:a), r y x -> c y) -> c x) ->
    forall (x:a), Accessible r x -> c x.
Proof. refine (
    fun (a:Type) =>
        fun (r:a -> a -> Prop) =>
            fun (c:a -> Type) => 
                fun (IH:forall (x:a), (forall (y:a), r y x -> c y) -> c x) =>
                    fix WFRecursion_F (x:a) (p:Accessible r x) : c x :=
                        IH x (fun (y:a) =>
                            fun (H:r y x) =>
                                WFRecursion_F y 
                                    (AccessibleInv a r x p y H))

).
Defined.

Definition WFRecursion_F: forall (a:Type) (r:a -> a -> Prop) (c:a -> Type),
    (forall (x:a), (forall (y:a), r y x -> c y) -> c x) ->
    forall (x:a), Accessible r x                        -> 
    c x :=
    fun (a:Type) =>
        fun (r:a -> a -> Prop) =>
            fun (c:a -> Type) => 
                fun (IH:forall (x:a), (forall (y:a), r y x -> c y) -> c x) =>
                    fix WFRecursion_F (x:a) (p:Accessible r x) : c x :=
                        IH x (fun (y:a) =>
                            fun (H:r y x) =>
                                WFRecursion_F y 
                                    (AccessibleInv a r x p y H)).
Check Fix.

(* Do it with 'refine' first: Attempting to re-define 'Fix'                     *)
Definition WFRecursion' : forall (a:Type) (r:a -> a -> Prop),
    WellFounded r -> 
    forall (c:a -> Type),
    (forall (x:a), (forall (y:a), r y x -> c y) -> c x) ->
    forall (x:a), c x.
Proof. refine (
    fun (a:Type) =>
        fun (r:a -> a -> Prop) =>
            fun (H:WellFounded r) =>
                fun (c:a -> Type) =>
                    fun (IH: forall (x:a), (forall (y:a), r y x -> c y) -> c x) =>
                        fun (x:a) => 
                            WFRecursion_F a r c IH x (H x)
).
Defined.

Definition WFRecursion : forall (a:Type) (r:a -> a -> Prop),
    WellFounded r -> 
    forall (c:a -> Type),
    (forall (x:a), (forall (y:a), r y x -> c y) -> c x) ->
    forall (x:a), c x 
    :=
    fun (a:Type) =>
        fun (r:a -> a -> Prop) =>
            fun (H:WellFounded r) =>
                fun (c:a -> Type) =>
                    fun (IH: forall (x:a), (forall (y:a), r y x -> c y) -> c x) =>
                        fun (x:a) => 
                            WFRecursion_F a r c IH x (H x).

