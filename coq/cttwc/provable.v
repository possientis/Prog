Inductive Provable : Prop -> Prop :=
| PA : forall (X Y:Prop), Provable (X -> Y) -> Provable X -> Provable Y
| PI : forall (X : Prop), Provable (X -> X)
| PK : forall (X Y:Prop), Provable Y -> Provable (X -> Y)
| PN : forall (X Y:Prop), Provable (X -> Y) -> Provable (~Y -> ~X)
| RE : forall (X Y:Prop), (X -> Y) -> Provable (X -> Y) (* dodgy ? *)
.

Definition Contradictory (X:Prop) : Prop := Provable (~X).
Definition Consistent (X:Prop) : Prop := ~Contradictory X.
Definition Independent (X:Prop) : Prop := ~Provable X /\ Consistent X.

Lemma L1 : forall (X Y:Prop), Provable (X -> Y) -> ~Provable Y -> ~Provable X.
Proof.
    intros X Y H1 H2 H3. apply H2. apply PA with X; assumption.
Qed.

Lemma L2 : forall (X Y:Prop), Provable (X -> Y) -> Consistent X -> Consistent Y.
Proof.
    unfold Consistent, Contradictory. intros X Y H1 H2 H3. apply H2.
    apply PA with (~Y).
    - apply PN. assumption.
    - assumption. 
Qed.

Lemma L3 : forall (X Y:Prop), Provable (X -> Y) -> Provable (Y -> X) ->
    Provable X -> Provable Y.
Proof.
    intros X Y H1 H2 H3. apply PA with X; assumption.
Qed.

Lemma L4 : forall (X Y:Prop), Provable (X -> Y) -> Provable (Y -> X) ->
    ~Provable X -> ~Provable Y.
Proof.
    intros X Y H1 H2 H3 H4. apply H3. apply L3 with Y; assumption.
Qed.

Lemma L5 : forall (X Y:Prop), Provable (X -> Y) -> Provable (Y -> X) ->
    Contradictory X -> Contradictory Y.
Proof.
    unfold Contradictory. intros X Y H1 H2 H3. apply PA with (~X).
    - apply PN. assumption.
    - assumption.
Qed.

Lemma L6 : forall (X Y:Prop), Provable (X -> Y) -> Provable (Y -> X) ->
    Consistent X -> Consistent Y.
Proof.
    unfold Consistent. intros X Y H1 H2 H3 H4. apply H3. 
    apply L5 with Y; assumption.
Qed.

Lemma L7 : forall (X Y:Prop), Provable (X -> Y) -> Provable (Y -> X) ->
    Independent X -> Independent Y.
Proof.
    unfold Independent. intros X Y H1 H2 [H3 H4]. split.
    - intros H5. apply H3. apply L3 with Y; assumption.
    - apply L6 with X; assumption.
Qed.


Lemma Sandwich : forall (Y:Prop),
    (exists (X Z:Prop), Provable (X -> Y) /\ Provable (Y -> Z) /\
        Consistent X /\ ~Provable Z) ->
    Independent Y.
Proof.
    intros Y [X [Z [H1 [H2 [H3 H4]]]]]. unfold Independent. split.
    - intros H5. apply H4. apply PA with Y; assumption.
    - unfold Consistent, Contradictory. intros H5.
      unfold Consistent in H3. unfold Contradictory in H3. apply H3.
      apply PA with (~Y).
        + apply PN. assumption.
        + assumption.
Qed.


Definition L8 : Prop := ~Provable False.
Definition L9 : Prop := Consistent (~False).
Definition L10: Prop :=  exists (X:Prop), Consistent X.
Definition L11: Prop := forall (X:Prop), Provable X -> Consistent X.

Lemma L12 : L8 -> L9.
Proof.
    unfold L8, L9, Consistent, Contradictory. intros H1 H2.
    apply H1. apply PA with (False -> False). 
    - assumption.
    - apply PI.
Qed.

Lemma L13 : L9 -> L10.
Proof.
    unfold L9, L10. intros H. exists (~False). assumption.
Qed.

Lemma L14 : L10 -> L8.
Proof.
    unfold L8, L10. intros [X H1]. unfold Consistent, Contradictory in H1.
    intros H2. apply H1. apply PK. assumption.
Qed.

Lemma L15 : L8 -> L11.
Proof.
    unfold L8, L11. intros H1 X H2. unfold Consistent, Contradictory.
    intros H3. apply H1, PA with X; assumption.
Qed.

Lemma L16 : L11 -> L8.
Proof.
    unfold L8, L11. intros H1 H2. apply (H1 False) in H2.
    unfold Consistent, Contradictory in H2. apply H2, PI.
Qed.

Definition PAPred (p:Prop -> Prop) : Prop := 
    forall (X Y:Prop), p (X -> Y) -> p X -> p Y.

Definition PIPred (p:Prop -> Prop) : Prop :=
    forall (X:Prop), p (X -> X).

Definition PKPred (p:Prop -> Prop) : Prop :=
    forall (X Y:Prop), p Y -> p (X -> Y).

Definition PNPred (p:Prop -> Prop) : Prop :=
    forall (X Y:Prop), p (X -> Y) -> p (~ Y -> ~ X).

Definition ProvPred (p:Prop -> Prop) : Prop :=
    PAPred p /\ PIPred p /\ PKPred p /\ PNPred p.

Definition PEPred (p:Prop -> Prop) : Prop :=
    forall (X:Prop), p False -> p X.

Lemma L17 : ProvPred (fun (X:Prop) => X).
Proof.
    unfold ProvPred, PAPred, PIPred, PKPred, PNPred. split.
    - intros X Y. auto.
    - split.
        + intros X. auto.
        + split.
            { intros X Y. auto. }
            { intros X Y. auto. }
Qed.

Lemma L18 : ProvPred (fun (_:Prop) => True).
Proof.
    unfold ProvPred, PAPred, PIPred, PKPred, PNPred. split.
    - intros X Y. auto.
    - split.
        + intros X. auto.
        + split.
            { intros X Y. auto. }
            { intros X Y. auto. }
Qed.

Lemma L19 : forall (X Y:Prop), 
    Provable (X -> Y) ->
    Consistent X      ->
    ~Provable Y       ->
    (Independent X) /\ (Independent Y).
Proof.
    intros X Y H1 H2 H3. split.
    - apply Sandwich. exists X, Y. split.
        + constructor.
        + split.
            { assumption. }
            { split; assumption. }
    - apply Sandwich. exists X, Y. split.
        + assumption.
        + split.
            { constructor. }
            { split; assumption. }
Qed.

Lemma L20 : forall (p:Prop -> Prop), PEPred p -> 
    ~ p False <-> ~ (forall (X:Prop), p X).
Proof.
    intros p. unfold PEPred.
    intros H1. split; intros H2 H3; apply H2.
    - apply H3.
    - intros X. apply H1. assumption.
Qed.

Inductive Formula : Set :=
| Bot : Formula
| Imp : Formula -> Formula -> Formula
.

(* Truth value semantics                                                        *)
Definition TVS : Prop := forall (X:Prop), X = True \/ X = False.

(* Excluded middle                                                              *)
Definition XM : Prop := forall (X:Prop), X \/ ~X.

(* Limited propositional ominscience                                            *)
(* Tests on numbers are either satisfiable or unsatisfiable                     *)
Definition LPO : Prop := forall (f:nat -> bool), 
    (exists n, f n = true) \/ ~(exists n, f n = true).

(* Markov principle                                                             *)
(* Tests on numbers which are not constantly false, are true for some numbers   *)
Definition Markov : Prop := forall (f:nat -> bool),
    ~(forall n, f n = false) -> exists n, f n = true.

(* Propositional extensionality                                                 *)
Definition PExt : Prop := forall (X Y:Prop), X <-> Y -> X = Y.

(* Proof irrelevance                                                            *)
Definition PIrr : Prop := forall (X:Prop) (a b:X), a = b.

(* functional extensionality                                                    *)
Definition FExt : Prop := forall (X Y:Type) (f g:X -> Y), 
    (forall (x:X), f x = g x) -> f = g.

Lemma L21 : TVS -> XM.
Proof.
    unfold TVS, XM. intros TVS X. destruct (TVS X) as [H|H].
    - left. rewrite H. trivial.
    - right. rewrite H. auto.
Qed.

Lemma L22 : XM -> LPO.
Proof.
    unfold XM, LPO. intros XM f. apply XM.
Qed.

Lemma L23 : LPO -> Markov.
Proof.
    unfold LPO, Markov. intros LPO f H1. destruct (LPO f) as [H2|H2].
    - assumption.
    - exfalso. apply H1. intros n. destruct (f n) eqn:E.
        + exfalso. apply H2. exists n. assumption.
        + reflexivity.
Qed.

Lemma L24 : TVS -> PExt.
Proof.
   unfold TVS, PExt. intros TVS X Y [H3 H4].
   destruct (TVS X) as [H1|H1]; destruct (TVS Y) as [H2|H2].
   - rewrite H1, H2. reflexivity.
   - exfalso. rewrite H1, H2 in H3. apply H3. trivial.
   - exfalso. rewrite H1, H2 in H4. apply H4. trivial.
   - rewrite H1, H2. reflexivity.
Qed.

Lemma L25 : XM -> PExt -> TVS.
Proof.
    unfold XM, PExt, TVS. intros XM PExt X.
    destruct (XM X) as [H|H].
    - left. apply PExt. split; intros H'.
        + trivial.
        + assumption.
    - right. apply PExt. split; intros H'.
        + apply H. assumption.
        + contradiction.
Qed.

Definition Pure (X:Prop) : Prop := forall (p q:X), p = q.

Lemma L26 : Pure True.
Proof.
    unfold Pure. intros p q. destruct p, q. reflexivity.
Qed.

Lemma L27 : forall (X:Prop), X -> X <-> True.
Proof.
    intros X p. split; intros H.
    - trivial.
    - assumption.
Qed.

Lemma L28 : PExt -> PIrr.
Proof.
    unfold PExt, PIrr. intros PExt X p q.
    assert (X = True) as H1.
        { apply PExt. apply L27. assumption. }
    assert (Pure X) as H2.
        { rewrite H1.  apply L26. } 
    unfold Pure in H2. apply H2.
Qed.

(* Proved at meta level                                                         *)
Axiom Ax29 : Consistent  (TVS /\ FExt).
Axiom Ax30 : ~Provable Markov /\ ~Provable PIrr /\ ~Provable FExt.

Lemma L31 : ~Provable False.
Proof.
    apply L14. exists (TVS /\ FExt). apply Ax29.
Qed.

Lemma L32 : Independent TVS.
Proof.
    apply Sandwich. exists (TVS /\ FExt), Markov. split.
    - apply RE. intros [H1 H2]. assumption.
    - split.
        + apply RE. intros H1. apply L23, L22, L21. assumption.
        + split.
            { apply Ax29. }
            { destruct Ax30 as [H1 [H2 H3]]. assumption. }
Qed.

Lemma L33 : Independent XM.
Proof.
    apply Sandwich. exists (TVS /\ FExt), Markov. split.
    - apply RE. intros [H1 H2]. apply L21. assumption.
    - split. 
        + apply RE.  intros H3. apply L23, L22. assumption.
        + split.
            { apply Ax29. }
            { destruct Ax30 as [H1 [H2 H3]]. assumption. }
Qed.

Lemma L34 : Independent LPO.
Proof.
    apply Sandwich. exists (TVS /\ FExt), Markov. split.
    - apply RE. intros [H1 H2]. apply L22, L21. assumption.
    - split.
        + apply RE. apply L23.
        + split.
            { apply Ax29. }
            { destruct Ax30 as [H1 [H2 H3]]. assumption. }
Qed.

Lemma L35 : Independent Markov.
Proof.
    apply Sandwich. exists (TVS /\ FExt), Markov. split.
    - apply RE. intros [H1 H2]. apply L23, L22, L21. assumption.
    - split.
        + apply PI.
        + split.
            { apply Ax29. }
            { destruct Ax30 as [H1 [H2 H3]]. assumption. }
Qed.

Lemma L36 : ~Provable PExt.
Proof.
    intros H1. destruct Ax30 as [H2 [H3 H4]]. apply H3.
    apply PA with PExt. 
    - apply RE, L28.
    - assumption.
Qed.

Lemma L37 : Independent PExt.
Proof.
    apply Sandwich. exists (TVS /\ FExt), PExt. split.
    - apply RE. intros [H1 H2]. apply L24. assumption.
    - split.
        + constructor.
        + split.
            { apply Ax29. }
            { apply L36. }
Qed.

Lemma L38 : Independent PIrr.
Proof.
    apply Sandwich. exists (TVS /\ FExt), PIrr. split.
    - apply RE. intros [H1 H2]. apply L28, L24. assumption.
    - split.
        + constructor.
        + split.
            { apply Ax29. }
            { destruct Ax30 as [H1 [H2 H3]]. assumption. }
Qed.

Lemma L39 : Independent FExt.
Proof.
    apply Sandwich. exists (TVS /\ FExt), FExt. split.
    - apply RE. intros [H1 H2]. assumption.
    - split.
        + constructor.
        + split.
            { apply Ax29. }
            { destruct Ax30 as [H1 [H2 H3]]. assumption. }
Qed.

(* Able to characterize TVS without reference to True and False.                *)
Lemma L40 : TVS <-> forall (X Y Z:Prop), X = Y \/ X = Z \/ Y = Z.
Proof.
    unfold TVS. split; intros H.
    - intros X Y Z. destruct (H X), (H Y), (H Z); subst; try (left; reflexivity).
        + right. left. reflexivity.
        + right. right. reflexivity.
        + right. right. reflexivity.
        + right. left. reflexivity.
    - intros X. destruct (H X True False) as [H1|[H1|H1]].
        + left. assumption.
        + right. assumption.
        + exfalso. rewrite <- H1. trivial.
Qed.


(* Able to characterize TVS without reference to True and False.                *)
Lemma L41 : TVS <-> forall (p:Prop -> Prop), p True -> p False -> forall X, p X.
Proof.
    unfold TVS. split; intros H.
    - intros p H1 H2 X. destruct (H X) as [H3|H3]; rewrite H3; assumption.
    - apply H.
        + left. reflexivity.
        + right. reflexivity.
Qed.

(* We cannot have a sort of TVS applicable to all types, only Prop's.           *)
Lemma L42 : ~ forall (X:Type), X = True \/ X = False.
Proof.
    intros H. destruct (H bool) as [H1|H1].
    - assert (forall (x y:True), x = y) as H2.
        { intros x y. destruct x, y. reflexivity. }
      rewrite <- H1 in H2. 
      assert (true = false) as H3.
        { apply H2. }
      inversion H3.
    - assert (exists (x:bool), True) as H2.
        { exists true. trivial. }
      rewrite H1 in H2. destruct H2 as [X H2]. assumption. 
Qed.

(* Implicational excluded middle.                                               *) 
Definition IXM : Prop := forall (X Y:Prop), (X -> Y) \/ (Y -> X).     

Lemma L43 : XM -> IXM.
Proof.
    unfold XM, IXM. intros H X Y. destruct (H Y) as [H1|H1].
    - left. intros _. assumption.
    - right. intros H2. apply H1 in H2. contradiction.
Qed.



Lemma L44 : Consistent IXM.
Proof.
    apply L2 with XM.
    - apply RE. apply L43.
    - destruct L33 as [H1 H2]. assumption.
Qed.

Axiom Ax45 : ~Provable IXM.
Axiom Ax46 : ~Provable (IXM -> XM).

(* Weak excluded middle                                                         *)
Definition WXM : Prop := forall (X:Prop), ~X \/ ~~X.

Lemma L45 : forall (A B:Prop), (A -> B) -> ~ B -> ~A.
Proof.
    intros A B H1 H2 H3. apply H2, H1, H3.
Qed.

Lemma L46 : WXM <-> forall (X:Prop), ~~X \/ ~~~X.
Proof.
    unfold WXM. split; intros H; intros X.
    - apply H.
    - destruct (H X) as [H'|H'].
        + right. assumption.
        + left. intros H1. apply H'. intros H2. apply H2. assumption.
Qed.

Lemma L47 : forall (A B:Prop), ~A \/ ~B -> ~(A /\ B).
Proof.
    intros A B [H1|H1] [H2 H3]; apply H1; assumption.
Qed.

Lemma L48 : forall (A:Prop), A -> ~~A.
Proof.
    intros A H1 H2. apply H2, H1.
Qed.

Lemma L49 : forall (A: Prop), ~A <-> ~~~A.
Proof.
    intros A. split; intros H1.
    - intros H2. apply H2. assumption.
    - intros H2. apply H1. intros H3. apply H3. assumption.
Qed.

Lemma L50 : forall (A B:Prop), ~A -> ~B -> ~(A \/ B).
Proof.
    intros A B H1 H2 [H3|H3].
    - apply H1. assumption.
    - apply H2. assumption.
Qed.


(*
Lemma L50 : WXM <-> forall (X Y:Prop), ~(X /\ Y) -> ~X \/ ~Y.
Proof.
    unfold WXM. split; intros H1 X.
    - intros Y H2. destruct (H1 X) as [H3|H3]; destruct (H1 Y) as [H4|H4].
        + left. assumption.
        + left. assumption.
        + right. assumption.
Show.
*)



