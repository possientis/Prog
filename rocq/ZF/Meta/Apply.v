Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Require Import ZF.Meta.Induction.
Require Import ZF.Meta.Shift.
Require Import ZF.Meta.Subst.
Require Import ZF.Meta.Syntax.

Import ListNotations.

(* An argument list selects actual terms for initial de Bruijn variables.       *)
Definition argT (args:Terms) (n:nat) : Term :=
  match nthT (revT args) n with
  | Some t => t
  | None   => Var (n - lengthT args)
  end.

(* Applying a schematic term substitutes its arguments into its body.           *)
Definition applyT (t:Term) (ts:Terms) : Term := substT (argT ts) t.

(* Argument lookup agrees with reversed argument lookup when it succeeds.       *)
Proposition ArgTNth : forall (ts:Terms) (n:nat) (t:Term),
  nthT (revT ts) n = Some t               ->
  argT ts n = t.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros ts n t H1. unfold argT. rewrite H1. reflexivity.
Qed.

(* Substitution preserves argument lookup when the lookup selects an argument.  *)
Proposition ArgTFromTsNth : forall (ts:Terms) (i:nat) (r:nat -> Term)
  (n:nat) (t:Term),
  nthT (revT ts) n = Some t               ->
  argT (fromTs i r ts) n = fromT i r t.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros ts i r n t H1.
  unfold argT.
  (* The reversed substituted list has the substituted selected argument.       *)
  assert (nthT (revT (fromTs i r ts)) n = Some (fromT i r t)) as H2. {
    rewrite <- RevT. apply NthT. assumption. }
  rewrite H2. reflexivity.
Qed.

(* Argument lookup past the supplied arguments returns a remaining variable.    *)
Proposition ArgTVar : forall (ts:Terms) (n:nat),
  lengthT ts <= n                         ->
  argT ts n = Var (n - lengthT ts).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros ts n H1.
  unfold argT.
  (* Past the length of the reversed argument list, lookup must fail.           *)
  assert (nthT (revT ts) n = None) as H2. {
    unfold nthT, lengthT.
    rewrite ToListRevT.
    apply nth_error_None. rewrite length_rev. assumption.
  }
  rewrite H2. reflexivity.
Qed.

(* Substituted argument lookup past the supplied arguments returns a variable.  *)
Proposition ArgTFromTsVar : forall (ts:Terms) (i:nat) (r:nat -> Term) (n:nat),
  lengthT ts <= n                         ->
  argT (fromTs i r ts) n = Var (n - lengthT ts).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros ts i r n H1.
  assert (lengthT (fromTs i r ts) = lengthT ts) as H2. { apply LengthT. }
  (* The substituted arguments have the same length, so lookup remains past it. *)
  assert (argT (fromTs i r ts) n = Var (n - lengthT (fromTs i r ts))) as H3. {
    apply ArgTVar. rewrite H2. assumption. }
  rewrite H3, H2. reflexivity.
Qed.

(* Applying arguments below a lifting lowers the lifting by their length.       *)
Proposition Shift :
  (forall (t:Term) (ts:Terms) (i k:nat),
    fromT k (argT ts) (Shift.fromT k (i + lengthT ts) t) =
    Shift.fromT k i t)                                                    /\
  (forall (p:Proof) (ts:Terms) (i k:nat),
    fromP k (argT ts) (Shift.fromP k (i + lengthT ts) p) =
    Shift.fromP k i p)                                                    /\
  (forall (us:Terms) (ts:Terms) (i k:nat),
    fromTs k (argT ts) (Shift.fromTs k (i + lengthT ts) us) =
    Shift.fromTs k i us).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply Induction.
  - intros ts i k. reflexivity.
  - intros ts i k. reflexivity.
  - intros n ts i k. simpl.
    (* A variable below the cutoff is untouched by both lifting and arguments.  *)
    destruct (n <? k) eqn:H1.
    + simpl. rewrite H1. reflexivity.
    + assert (k <= n) as H2. { apply Nat.ltb_ge. assumption. }
      assert ((n + (i + lengthT ts) <? k) = false) as H3. {
        apply Nat.ltb_ge.
        apply Nat.le_trans with (m := n). 1: assumption.
        apply Nat.le_add_r. }
      simpl. rewrite H3.
      assert (lengthT ts <= n + (i + lengthT ts) - k) as H4. {
        rewrite Nat.add_sub_swap. 2: assumption.
        apply Nat.le_trans with (m := i + lengthT ts).
        1: apply Nat.le_add_l. apply Nat.le_add_l. }
      rewrite ArgTVar. 2: assumption.
      simpl.
      assert (n + (i + lengthT ts) - k - lengthT ts + k = n + i) as H5. {
        assert (n + (i + lengthT ts) - k = n - k + (i + lengthT ts)) as H5. {
          apply Nat.add_sub_swap. assumption. }
        rewrite H5.
        assert (n - k + (i + lengthT ts) - lengthT ts = n - k + i) as H6. {
          rewrite <- Nat.add_sub_assoc. 2: apply Nat.le_add_l.
          rewrite Nat.add_sub. reflexivity. }
        rewrite H6. rewrite Nat.add_comm.
        rewrite Nat.add_assoc. rewrite Nat.add_comm with (n := k) (m := n - k).
        rewrite Nat.sub_add. 2: assumption.
        reflexivity. }
      unfold shiftT. simpl. rewrite H5. reflexivity.
  - intros ty ts i k. reflexivity.
  - intros name args IH ts i k. simpl. rewrite IH. reflexivity.
  - intros x y IH1 IH2 ts i k. simpl. rewrite IH1, IH2. reflexivity.
  - intros x y IH1 IH2 ts i k. simpl. rewrite IH1, IH2. reflexivity.
  - intros x y IH1 IH2 ts i k. simpl. rewrite IH1, IH2. reflexivity.
  - intros x y IH1 IH2 ts i k. simpl. rewrite IH1, IH2. reflexivity.
  - intros x y IH1 IH2 ts i k. simpl. rewrite IH1, IH2. reflexivity.
  - intros x y IH1 IH2 ts i k. simpl. rewrite IH1, IH2. reflexivity.
  - intros x y IH1 IH2 ts i k. simpl. rewrite IH1, IH2. reflexivity.
  - intros p q IH1 IH2 ts i k. simpl. rewrite IH1, IH2. reflexivity.
  - intros p q IH1 IH2 ts i k. simpl. rewrite IH1, IH2. reflexivity.
  - intros p q IH1 IH2 ts i k. simpl. rewrite IH1, IH2. reflexivity.
  - intros p q IH1 IH2 ts i k. simpl. rewrite IH1, IH2. reflexivity.
  - intros p IH ts i k. simpl. rewrite IH. reflexivity.
  - intros p IH ts i k. simpl. rewrite IH. reflexivity.
  - intros p IH ts i k. simpl. rewrite IH. reflexivity.
  - intros p IH ts i k. simpl. rewrite IH. reflexivity.
  - intros A x IH1 IH2 ts i k. simpl. rewrite IH1, IH2. reflexivity.
  - intros A p q IH1 IH2 IH3 ts i k. simpl.
    rewrite IH1, IH2, IH3. reflexivity.
  - intros t IH ts i k. simpl. rewrite IH. reflexivity.
  - intros t IH ts i k. simpl. rewrite IH. reflexivity.
  - intros name us IH ts i k. simpl. rewrite IH. reflexivity.
  - intros ts i k. reflexivity.
  - intros t us IH1 IH2 ts i k. simpl. rewrite IH1, IH2. reflexivity.
Qed.

(* Substitution through application acts on the body and the arguments.         *)
Proposition From :
  (forall (t:Term) (ts:Terms) (i k:nat) (r:nat -> Term),
    fromT (k + i) r (fromT k (argT ts) t) =
    fromT k (argT (fromTs i r ts))
      (fromT (k + i + lengthT ts) r t))                                  /\
  (forall (p:Proof) (ts:Terms) (i k:nat) (r:nat -> Term),
    fromP (k + i) r (fromP k (argT ts) p) =
    fromP k (argT (fromTs i r ts))
      (fromP (k + i + lengthT ts) r p))                                  /\
  (forall (us:Terms) (ts:Terms) (i k:nat) (r:nat -> Term),
    fromTs (k + i) r (fromTs k (argT ts) us) =
    fromTs k (argT (fromTs i r ts))
      (fromTs (k + i + lengthT ts) r us)).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply Induction.
  - intros ts i k r. reflexivity.
  - intros ts i k r. reflexivity.
  - intros n ts i k r. simpl.
    (* Variables before the argument cutoff are not affected by either side.    *)
    destruct (n <? k) eqn:H1.
    + assert ((n <? k + i + lengthT ts) = true) as H2. {
        apply Nat.ltb_lt. apply Nat.ltb_lt in H1.
        apply Nat.lt_le_trans with (m := k). 1: assumption.
        apply Nat.le_trans with (m := k + i).
        1: apply Nat.le_add_r. apply Nat.le_add_r. }
      assert ((n <? k + i) = true) as H3. {
        apply Nat.ltb_lt. apply Nat.ltb_lt in H1.
        apply Nat.lt_le_trans with (m := k).
        1: assumption. apply Nat.le_add_r. }
      simpl. rewrite H3. rewrite H2. simpl. rewrite H1. reflexivity.
    + assert (k <= n) as H2. { apply Nat.ltb_ge. assumption. }
      (* Variables in the argument block are supplied by substituted arguments. *)
      destruct (Nat.lt_ge_cases (n - k) (lengthT ts)) as [H3|H3].
      * destruct (nthT (revT ts) (n - k)) as [t|] eqn:H4.
        -- assert ((n <? k + i + lengthT ts) = true) as H5. {
             apply Nat.ltb_lt.
             rewrite <- (Nat.sub_add k n). 2: assumption.
             apply Nat.lt_le_trans with (m := lengthT ts + k).
             1: apply Nat.add_lt_mono_r; assumption.
             rewrite Nat.add_comm. rewrite <- Nat.add_assoc.
             apply Nat.add_le_mono.
             1: reflexivity. apply Nat.le_add_l. }
           rewrite (ArgTNth ts (n - k) t). 2: assumption.
           unfold shiftT. rewrite ShiftFromT.
           rewrite H5. simpl. rewrite H1.
           rewrite (ArgTFromTsNth ts i r (n - k) t). 2: assumption.
           reflexivity.
        -- assert (nthT (revT ts) (n - k) = None) as H5. { assumption. }
           unfold nthT in H5. apply nth_error_None in H5.
           unfold lengthT in H3. rewrite ToListRevT in H5.
           rewrite length_rev in H5. apply Nat.nle_gt in H3. contradiction.
      * assert (argT ts (n - k) = Var (n - k - lengthT ts)) as H4. {
          apply ArgTVar. assumption. }
        rewrite H4. unfold shiftT. simpl.
        destruct (n <? k + i + lengthT ts) eqn:H5.
        -- assert ((n - k - lengthT ts + k <? k + i) = true) as H6. {
             apply Nat.ltb_lt.
             assert (n - k < i + lengthT ts) as H6. {
               apply (proj2 (Nat.add_lt_mono_l (n - k)
                 (i + lengthT ts) k)).
               assert (n < k + i + lengthT ts) as H6. {
                 apply Nat.ltb_lt. assumption. }
               rewrite <- (Nat.sub_add k n) in H6. 2: assumption.
               rewrite Nat.add_comm with (n := n - k) (m := k) in H6.
               rewrite <- Nat.add_assoc in H6. assumption. }
             assert (n - k - lengthT ts < i) as H7. {
               apply (proj2 (Nat.add_lt_mono_r (n - k - lengthT ts)
                 i (lengthT ts))).
               rewrite Nat.sub_add. 2: assumption. assumption. }
             rewrite Nat.add_comm.
             apply (proj1 (Nat.add_lt_mono_l (n - k - lengthT ts) i k)).
             assumption. }
           rewrite H6. simpl. rewrite H1.
           rewrite ArgTFromTsVar. 2: assumption.
           unfold shiftT. simpl. reflexivity.
        -- assert ((n - k - lengthT ts + k <? k + i) = false) as H6. {
             apply Nat.ltb_ge.
             assert (i + lengthT ts <= n - k) as H6. {
               assert (k + i + lengthT ts <= n) as H6. {
                 apply Nat.ltb_ge. assumption. }
               apply Nat.le_trans with (m := (k + i + lengthT ts) - k).
               2: apply Nat.sub_le_mono_r; assumption.
               assert (k + i + lengthT ts - k = i + lengthT ts) as H7. {
                 assert (k + i + lengthT ts = i + lengthT ts + k) as H7. {
                   rewrite <- Nat.add_assoc.
                   rewrite Nat.add_comm with (n := k) (m := i + lengthT ts).
                   reflexivity. }
                 rewrite H7. rewrite Nat.add_sub. reflexivity. }
               rewrite H7. reflexivity. }
             assert (i <= n - k - lengthT ts) as H7. {
               apply (proj2 (Nat.add_le_mono_r i
                 (n - k - lengthT ts) (lengthT ts))).
               rewrite Nat.sub_add.
               2: apply Nat.le_trans with (m := i + lengthT ts);
                  [apply Nat.le_add_l|assumption]. assumption. }
             assert (n - k - lengthT ts + k =
               k + (n - k - lengthT ts)) as H8. {
               rewrite Nat.add_comm. reflexivity. }
             rewrite H8. apply Nat.add_le_mono.
             1: reflexivity. assumption. }
           rewrite H6. simpl.
           assert (n - k - lengthT ts + k - (k + i) =
             n - (k + i + lengthT ts)) as H7. {
             rewrite Nat.sub_add_distr. rewrite Nat.add_sub.
             assert (k + i + lengthT ts = k + lengthT ts + i) as H7. {
               rewrite <- Nat.add_assoc.
               rewrite Nat.add_comm with (n := i) (m := lengthT ts).
               rewrite Nat.add_assoc. reflexivity. }
             rewrite H7. rewrite Nat.sub_add_distr.
             rewrite Nat.sub_add_distr. reflexivity. }
           rewrite H7.
           rewrite <- (LengthT ts i r).
           assert (Shift.fromT 0 (k + i + lengthT (fromTs i r ts))
             (r (n - (k + i + lengthT (fromTs i r ts)))) =
             Shift.fromT k (i + lengthT (fromTs i r ts))
               (shiftT k (r (n - (k + i + lengthT (fromTs i r ts)))))) as H8. {
             unfold shiftT at 1.
             assert (Shift.fromT 0 k
               (r (n - (k + i + lengthT (fromTs i r ts)))) =
               shiftT (k + 0)
                 (r (n - (k + i + lengthT (fromTs i r ts))))) as H8. {
               unfold shiftT. rewrite Nat.add_0_r. reflexivity. }
             rewrite H8.
             rewrite (Shift.FromShiftT
               (r (n - (k + i + lengthT (fromTs i r ts)))) k
               (i + lengthT (fromTs i r ts)) 0).
             unfold shiftT.
             assert (k + (i + lengthT (fromTs i r ts)) + 0 =
               k + i + lengthT (fromTs i r ts)) as H9. {
               rewrite Nat.add_0_r. rewrite Nat.add_assoc. reflexivity. }
             rewrite H9. reflexivity. }
           rewrite H8.
           rewrite (proj1 Shift
             (shiftT k (r (n - (k + i + lengthT (fromTs i r ts)))))
             (fromTs i r ts) i k).
           unfold shiftT at 2.
           assert (Shift.fromT 0 k
             (r (n - (k + i + lengthT (fromTs i r ts)))) =
             shiftT (k + 0)
               (r (n - (k + i + lengthT (fromTs i r ts))))) as H9. {
             unfold shiftT. rewrite Nat.add_0_r. reflexivity. }
           rewrite H9.
           rewrite (Shift.FromShiftT
             (r (n - (k + i + lengthT (fromTs i r ts)))) k i 0).
           assert (k + i + 0 = k + i) as H10. {
             rewrite Nat.add_0_r. reflexivity. }
           unfold shiftT at 1. rewrite H10.
           reflexivity.
  - intros ty ts i k r. reflexivity.
  - intros name args IH ts i k r. simpl. rewrite IH. reflexivity.
  - intros x y IH1 IH2 ts i k r. simpl. rewrite IH1, IH2. reflexivity.
  - intros x y IH1 IH2 ts i k r. simpl. rewrite IH1, IH2. reflexivity.
  - intros x y IH1 IH2 ts i k r. simpl. rewrite IH1, IH2. reflexivity.
  - intros x y IH1 IH2 ts i k r. simpl. rewrite IH1, IH2. reflexivity.
  - intros x y IH1 IH2 ts i k r. simpl. rewrite IH1, IH2. reflexivity.
  - intros x y IH1 IH2 ts i k r. simpl. rewrite IH1, IH2. reflexivity.
  - intros x y IH1 IH2 ts i k r. simpl. rewrite IH1, IH2. reflexivity.
  - intros p q IH1 IH2 ts i k r. simpl. rewrite IH1, IH2. reflexivity.
  - intros p q IH1 IH2 ts i k r. simpl. rewrite IH1, IH2. reflexivity.
  - intros p q IH1 IH2 ts i k r. simpl. rewrite IH1, IH2. reflexivity.
  - intros p q IH1 IH2 ts i k r. simpl. rewrite IH1, IH2. reflexivity.
  - intros p IH ts i k r. simpl. rewrite IH. reflexivity.
  - intros p IH ts i k r. simpl.
    assert (S (k + i) = S k + i) as H1. { reflexivity. }
    rewrite H1.
    assert (S (k + i + lengthT ts) = S k + i + lengthT ts) as H2. {
      reflexivity. }
    rewrite H2. rewrite IH. reflexivity.
  - intros p IH ts i k r. simpl.
    assert (S (k + i) = S k + i) as H1. { reflexivity. }
    rewrite H1.
    assert (S (k + i + lengthT ts) = S k + i + lengthT ts) as H2. {
      reflexivity. }
    rewrite H2. rewrite IH. reflexivity.
  - intros p IH ts i k r. simpl.
    assert (S (k + i) = S k + i) as H1. { reflexivity. }
    rewrite H1.
    assert (S (k + i + lengthT ts) = S k + i + lengthT ts) as H2. {
      reflexivity. }
    rewrite H2. rewrite IH. reflexivity.
  - intros A x IH1 IH2 ts i k r. simpl. rewrite IH1, IH2. reflexivity.
  - intros A p q IH1 IH2 IH3 ts i k r. simpl.
    rewrite IH1, IH2, IH3. reflexivity.
  - intros t IH ts i k r. simpl. rewrite IH. reflexivity.
  - intros t IH ts i k r. simpl. rewrite IH. reflexivity.
  - intros name us IH ts i k r. simpl. rewrite IH. reflexivity.
  - intros ts i k r. reflexivity.
  - intros t us IH1 IH2 ts i k r. simpl. rewrite IH1, IH2. reflexivity.
Qed.

(* Substitution through an applied term substitutes body and arguments.         *)
Proposition FromT : forall (t:Term) (ts:Terms) (i:nat) (r:nat -> Term),
  fromT i r (applyT t ts) =
  applyT (fromT (i + lengthT ts) r t) (fromTs i r ts).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros t ts i r. unfold applyT, substT.
  assert (i = 0 + i) as H1. { reflexivity. }
  rewrite H1. apply From.
Qed.
