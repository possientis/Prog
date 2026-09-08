Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Require Import ZF.Meta.Induction.
Require Import ZF.Meta.Shift.
Require Import ZF.Meta.Syntax.

(* Substitution at level i leaves lower bound variables and replaces the rest.  *)
Fixpoint fromT (i:nat) (r:nat -> Term) (t:Term) : Term :=
  match t with
  | Bot              => Bot
  | Top              => Top
  | Var n            => if n <? i then Var n else shiftT i (r (n - i))
  | HoleT ty         => HoleT ty
  | IdentT name args => IdentT name (fromTs i r args)
  | Elem x y         => Elem  (fromT i r x) (fromT i r y)
  | Leq x y          => Leq   (fromT i r x) (fromT i r y)
  | Geq x y          => Geq   (fromT i r x) (fromT i r y)
  | Lt x y           => Lt    (fromT i r x) (fromT i r y)
  | Gt x y           => Gt    (fromT i r x) (fromT i r y)
  | Equal x y        => Equal (fromT i r x) (fromT i r y)
  | NotEq x y        => NotEq (fromT i r x) (fromT i r y)
  | Imp p q          => Imp   (fromT i r p) (fromT i r q)
  | Iff p q          => Iff   (fromT i r p) (fromT i r q)
  | And p q          => And   (fromT i r p) (fromT i r q)
  | Or p q           => Or    (fromT i r p) (fromT i r q)
  | Not p            => Not   (fromT i r p)
  | All p            => All   (fromT (S i) r p)
  | Ex p             => Ex    (fromT (S i) r p)
  | Lam p            => Lam   (fromT (S i) r p)
  | App A x          => App   (fromT i r A) (fromT i r x)
  | Def A p q        => Def   (fromT i r A) (fromP i r p) (fromP i r q)
  end
with fromP (i:nat) (r:nat -> Term) (p:Proof) : Proof :=
  match p with
  | HoleP t        => HoleP (fromT i r t)
  | AxiomP t       => AxiomP (fromT i r t)
  | IdentP name ts => IdentP name (fromTs i r ts)
  end
with fromTs (i:nat) (r:nat -> Term) (ts:Terms) : Terms :=
  match ts with
  | NilT       => NilT
  | ConsT t ts => ConsT (fromT i r t) (fromTs i r ts)
  end.

Definition substT (r:nat -> Term) (t:Term)  : Term := fromT 0 r t.

Definition substP (r:nat -> Term) (p:Proof) : Proof := fromP 0 r p.

(* Substitution through term arguments preserves their length.                  *)
Proposition LengthT : forall (ts:Terms) (i:nat) (r:nat -> Term),
  lengthT (fromTs i r ts) = lengthT ts.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros ts i r.
  (* The empty argument list has the same length after substitution.            *)
  induction ts as [|t ts IH]. 1: reflexivity.
  (* A non-empty list keeps one head and substitutes through the tail.          *)
  unfold lengthT. unfold lengthT in IH. simpl. rewrite IH. reflexivity.
Qed.

(* Substitution through appended term arguments acts on each side.              *)
Proposition AppT : forall (ts us:Terms) (i:nat) (r:nat -> Term),
  fromTs i r (appT ts us) = appT (fromTs i r ts) (fromTs i r us).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros ts us i r.
  (* The empty left side leaves only the substituted right side.                *)
  induction ts as [|t ts IH]. 1: reflexivity.
  (* A non-empty left side keeps its substituted head and recurses on the tail. *)
  simpl. rewrite IH. reflexivity.
Qed.

(* Substitution through reversed term arguments reverses substituted arguments. *)
Proposition RevT : forall (ts:Terms) (i:nat) (r:nat -> Term),
  fromTs i r (revT ts) = revT (fromTs i r ts).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros ts i r.
  (* The empty argument list is unchanged by both substitution and reversal.    *)
  induction ts as [|t ts IH]. 1: reflexivity.
  (* Reversal and substitution commute by the append compatibility.             *)
  simpl. rewrite AppT. rewrite IH. reflexivity.
Qed.

(* Substitution through term arguments preserves successful lookup.             *)
Proposition NthT : forall (ts:Terms) (i:nat) (r:nat -> Term) (n:nat) (t:Term),
  nthT ts n = Some t -> nthT (fromTs i r ts) n = Some (fromT i r t).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros ts i r n t H1.
  revert n t H1.
  (* Lookup in the empty argument list cannot succeed.                          *)
  induction ts as [|u ts IH]; intros n t H1.
  - destruct n as [|n]; discriminate.
  - destruct n as [|n].
    + (* The first lookup returns the substituted first argument.               *)
      inversion H1. subst. reflexivity.
    + (* Later lookups are preserved by the induction hypothesis.               *)
      apply IH. assumption.
Qed.

(* Substitution above a lifting commutes with the lifting.                      *)
Proposition ShiftFrom :
  (forall (t:Term) (i j k:nat) (r:nat -> Term),
    fromT (i + j + k) r (Shift.fromT i j t) =
    Shift.fromT i j (fromT (i + k) r t))                                   /\
  (forall (p:Proof) (i j k:nat) (r:nat -> Term),
    fromP (i + j + k) r (Shift.fromP i j p) =
    Shift.fromP i j (fromP (i + k) r p))                                   /\
  (forall (ts:Terms) (i j k:nat) (r:nat -> Term),
    fromTs (i + j + k) r (Shift.fromTs i j ts) =
    Shift.fromTs i j (fromTs (i + k) r ts)).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply Induction.
  - intros i j k r. reflexivity.
  - intros i j k r. reflexivity.
  - intros n i j k r. simpl.
    (* A variable below the lifting cutoff is below all related cutoffs.        *)
    destruct (n <? i) eqn:H1.
    + assert (n < i) as H2. { apply Nat.ltb_lt. assumption. }
      assert ((n <? i + j + k) = true) as H3. {
        apply Nat.ltb_lt.
        apply Nat.lt_le_trans with (m := i).
        1: assumption.
        apply Nat.le_trans with (m := i + j).
        1: apply Nat.le_add_r.
        apply Nat.le_add_r. }
      assert ((n <? i + k) = true) as H4. {
        apply Nat.ltb_lt.
        apply Nat.lt_le_trans with (m := i).
        1: assumption.
        apply Nat.le_add_r. }
      simpl. rewrite H3, H4. simpl. rewrite H1. reflexivity.
    + assert (i <= n) as H2. { apply Nat.ltb_ge. assumption. }
      (* Variables in and after the lifted block split around the substitution. *)
      destruct (n <? i + k) eqn:H3.
      * assert (n < i + k) as H4. { apply Nat.ltb_lt. assumption. }
        assert ((n + j <? i + j + k) = true) as H5. {
          apply Nat.ltb_lt.
          assert (i + j + k = i + k + j) as H5. {
            rewrite <- Nat.add_assoc.
            rewrite (Nat.add_comm j k).
            rewrite Nat.add_assoc. reflexivity. }
          rewrite H5.
          apply Nat.add_lt_mono_r. assumption. }
        simpl. rewrite H5, H1. reflexivity.
      * assert (i + k <= n) as H4. { apply Nat.ltb_ge. assumption. }
        assert ((n + j <? i + j + k) = false) as H5. {
          apply Nat.ltb_ge.
          assert (i + j + k = i + k + j) as H5. {
            rewrite <- Nat.add_assoc.
            rewrite (Nat.add_comm j k).
            rewrite Nat.add_assoc. reflexivity. }
          rewrite H5.
          apply Nat.add_le_mono_r. assumption. }
        simpl. rewrite H5.
        assert (n + j - (i + j + k) = n - (i + k)) as H6. {
          assert (i + j + k = i + k + j) as H6. {
            rewrite <- Nat.add_assoc.
            rewrite (Nat.add_comm j k).
            rewrite Nat.add_assoc. reflexivity. }
          rewrite H6. rewrite Nat.sub_add_distr.
          rewrite Nat.add_sub_swap. 2: assumption.
          rewrite Nat.add_sub. reflexivity. }
        rewrite H6. rewrite Shift.FromShiftT. reflexivity.
  - intros ty i j k r. reflexivity.
  - intros name args IH i j k r. simpl. rewrite IH. reflexivity.
  - intros x y IH1 IH2 i j k r. simpl. rewrite IH1, IH2. reflexivity.
  - intros x y IH1 IH2 i j k r. simpl. rewrite IH1, IH2. reflexivity.
  - intros x y IH1 IH2 i j k r. simpl. rewrite IH1, IH2. reflexivity.
  - intros x y IH1 IH2 i j k r. simpl. rewrite IH1, IH2. reflexivity.
  - intros x y IH1 IH2 i j k r. simpl. rewrite IH1, IH2. reflexivity.
  - intros x y IH1 IH2 i j k r. simpl. rewrite IH1, IH2. reflexivity.
  - intros x y IH1 IH2 i j k r. simpl. rewrite IH1, IH2. reflexivity.
  - intros p q IH1 IH2 i j k r. simpl. rewrite IH1, IH2. reflexivity.
  - intros p q IH1 IH2 i j k r. simpl. rewrite IH1, IH2. reflexivity.
  - intros p q IH1 IH2 i j k r. simpl. rewrite IH1, IH2. reflexivity.
  - intros p q IH1 IH2 i j k r. simpl. rewrite IH1, IH2. reflexivity.
  - intros p IH i j k r. simpl. rewrite IH. reflexivity.
  - intros p IH i j k r. simpl.
    assert (S (i + j + k) = S i + j + k) as H1. { reflexivity. }
    rewrite H1. rewrite IH. reflexivity.
  - intros p IH i j k r. simpl.
    assert (S (i + j + k) = S i + j + k) as H1. { reflexivity. }
    rewrite H1. rewrite IH. reflexivity.
  - intros p IH i j k r. simpl.
    assert (S (i + j + k) = S i + j + k) as H1. { reflexivity. }
    rewrite H1. rewrite IH. reflexivity.
  - intros A x IH1 IH2 i j k r. simpl. rewrite IH1, IH2. reflexivity.
  - intros A p q IH1 IH2 IH3 i j k r. simpl.
    rewrite IH1, IH2, IH3. reflexivity.
  - intros t IH i j k r. simpl. rewrite IH. reflexivity.
  - intros t IH i j k r. simpl. rewrite IH. reflexivity.
  - intros name ts IH i j k r. simpl. rewrite IH. reflexivity.
  - intros i j k r. reflexivity.
  - intros t ts IH1 IH2 i j k r. simpl. rewrite IH1, IH2. reflexivity.
Qed.

(* Substitution above a full lifting commutes with the full lifting.            *)
Proposition ShiftFromT : forall (t:Term) (i j:nat) (r:nat -> Term),
  fromT (i + j) r (shiftT i t) = shiftT i (fromT j r t).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros t i j r. unfold shiftT.
  assert (0 + i + j = i + j) as H1. { reflexivity. }
  assert (0 + j = j) as H2. { reflexivity. }
  rewrite <- H1. rewrite <- H2. apply ShiftFrom.
Qed.
