Require Import Nat.

Inductive Sig (a:Type) (p:a -> Type) : Type :=
| Ex : forall (x:a), p x -> Sig a p
.

Arguments Sig {a}.
Arguments Ex {a} {p}.


(* Elim restriction, cant do the obvious. However, see below...                 *)
Definition witnessFail : forall (f:nat -> bool),
    (exists (n:nat), f n = true) -> Sig (fun n => f n = true).
Proof.
Admitted.

Definition Guarded (f:nat -> bool) (n:nat) : Prop :=
    exists (k:nat), f (n + k) = true.

Lemma L1 : forall (f:nat -> bool) (n:nat), f n = true -> Guarded f n.
Proof.
    intros f n H. exists 0. rewrite <- plus_n_O. assumption.
Qed.

Lemma L2 : forall (f:nat -> bool) (n:nat), Guarded f (S n) -> Guarded f n.
Proof.
    intros f n [k H1]. exists (S k). rewrite <- plus_n_Sm. assumption.
Qed.

Lemma L3 : forall (f:nat -> bool), (exists (k:nat), f k = true) -> Guarded f 0.
Proof.
    intros f [k H1]. exists k. assumption.
Qed.

Lemma L4 : forall (f:nat -> bool) (n:nat), 
    Guarded f n -> f n = false -> Guarded f (S n).
Proof.
    intros f n [k H1] H2. destruct k as [|k].
    - rewrite <- plus_n_O in H1. rewrite H1 in H2. inversion H2.
    - exists k. rewrite <- plus_n_Sm in H1. assumption.
Qed.

(* G f n is equivalent to (exists (k:nat), f (n + k) = true), but this is far   *)
(* from obvious at this stage (see Lemma L13). This definition is miraculous    *)
Inductive G (f:nat -> bool) : nat -> Prop :=
| mkG : forall (n:nat), (f n = false -> G f (S n)) -> G f n
.

Lemma L5 : forall (f:nat -> bool) (n:nat), f n = true -> G f n.
Proof.
    intros f n H1. constructor. intros H2. rewrite H1 in H2. inversion H2.
Defined.

Lemma L6 : forall (f:nat -> bool) (n:nat), G f (S n) -> G f n.
Proof.
    intros f n H1. constructor. intros H2. assumption.    
Defined.

Lemma L7 : forall (f:nat -> bool) (n:nat), G f n -> G f 0.
Proof.
    intros f. induction n as [|n IH].
    - auto.
    - intros H1. apply IH. apply L6. assumption.
Defined.


Lemma L8 : forall (f:nat -> bool), (exists (n:nat), f n = true) -> G f 0.
Proof.
    intros f [n H1].  apply L7 with n. apply L5. assumption.
Qed.

Definition elimG 
    (f:nat -> bool) 
    (p:nat -> Type)
    (g: forall (n:nat), (f n = false -> p (S n)) -> p n)
    : forall (n:nat), G f n -> p n 
    := fix k (n:nat) (H:G f n) : p n := g n 
        (fun e => k (S n) 
            ( match H with
              | mkG _ _ H => H
              end e)).

Definition L9 : forall (f:nat -> bool) (n:nat), 
    G f n -> Sig (fun k => f k = true).
Proof.
    intro f. apply elimG. intros n H1. destruct (f n) eqn:E.
    - exact (Ex n E).
    - apply H1. reflexivity.
Defined.

(* This is quite a remarkable fact. We can write a function which given a proof *)
(* that something holds for some n, will return a witness of the fact.          *)
(* However, in some way there is nothing surprising: keep looping               *) 
Theorem witness : forall (f:nat -> bool),
    (exists (n:nat), f n = true) -> Sig (fun n => f n = true).
Proof.
    intros f H1. apply L9 with 0. destruct H1 as [n H1].
    apply L7 with n. apply L5. assumption.
Defined.

Definition f1 (n:nat) : bool := eqb n 10.

Lemma L10 : exists (n:nat), f1 n = true.
Proof.
    exists 10. reflexivity.
Defined.

(* Very cool                                                                    *)
Compute witness f1 L10.


Lemma L11 : forall (f:nat -> bool) (k n:nat),
    f(n + k) = true -> G f n.
Proof.
    intros f. induction k as [|k IH]; intros n.
    - rewrite <- plus_n_O. apply L5.
    - rewrite <- plus_n_Sm. intros H1. apply L6, IH. assumption.
Qed.

(* Improvement on L9                                                            *)
Definition L12 : forall (f:nat -> bool) (n:nat), 
    G f n -> Sig (fun k => f (n + k) = true).
Proof.
    intro f. apply elimG. intros n H1. destruct (f n) eqn:E. 
    - assert (f (n + 0) = true) as E'. { rewrite <- plus_n_O. assumption. }
      exact (Ex 0 E').
    - destruct (H1 eq_refl) as [k H2].
      assert (f (n + S k) = true) as H3. { rewrite <- plus_n_Sm. assumption. }
      exact (Ex (S k) H3).
Qed. 

Lemma L13 : forall (f:nat -> bool) (n:nat), 
    G f n <-> exists (k:nat), f(n + k) = true.
Proof.
    intros f n. split.
    - intros H1. remember (L12 f n H1) as e eqn:E. clear E. destruct e as [k H2].
      exists k. assumption.
    - intros [k H1]. apply L11 with k. assumption.
Qed.

Lemma L14 : forall (f:nat -> bool), 
    (exists (n:nat), f n = true) <-> G f 0.
Proof.
    intros f. split.
    - intros [n H1]. apply L7 with n. apply L5. assumption.
    - intros H1. apply (L13 f 0). assumption.
Qed.

Lemma L15 : forall (f:nat -> bool),
    Sig (fun n => f n = true) -> exists (n:nat), f n = true.
Proof.
    intros f [n H1]. exists n. assumption.
Qed.

Definition L16 : forall (f:bool -> bool),
    (exists (b:bool), f b = true) -> Sig (fun b => f b = true).
Proof.
    intros f H1. destruct (f true) eqn:E1; destruct (f false) eqn:E2.
    - exact (Ex true E1).
    - exact (Ex true E1).
    - exact (Ex false E2).
    - exfalso. destruct H1 as [b H1]. destruct b eqn:E.
        + rewrite H1 in E1. inversion E1.
        + rewrite H1 in E2. inversion E2.
Defined.

Lemma L17 : exists (b:bool), negb b = true.
Proof.
    exists false. reflexivity.
Qed.

Lemma L18 : exists (b:bool), (fun b => b) b = true.
Proof.
    exists true. reflexivity.
Qed.

Lemma L19 : exists (b:bool), (fun b => true) b = true.
Proof.
    exists true. reflexivity.
Qed.

Lemma L20 : exists (b:bool), (fun b => true) b = true.
Proof.
    exists false. reflexivity.
Qed.

Compute L16 negb L17.
Compute L16 (fun b => b) L18.
Compute L16 (fun b => true) L19.
Compute L16 (fun b => true) L20.

Definition L21 : forall (p:nat -> Prop),
    (forall (n:nat), {p n} + {~ p n}) ->
    (exists (n:nat), p n) -> 
    Sig p.
Proof.
    intros p q H1. remember (fun n => 
        match q n with
        | left _    => true
        | right _   => false
        end) as f eqn:F.
    assert (exists (n:nat), f n = true) as H2.
        { destruct H1 as [n H1]. exists n. rewrite F. destruct (q n) as [H2|H2].
            { reflexivity. }
            { exfalso. apply H2. assumption. }}
    remember (witness f H2) as e eqn:E. destruct e as [n H3].
    assert (p n) as H4.
        { clear E. rewrite F in H3. destruct (q n) as [H4|H4].
            { assumption . }
            { inversion H3. }}
    exact (Ex n H4).
Defined.


Lemma L22 : forall (f g:nat -> bool), 
    (exists (n:nat), f n = true \/ g n = true) 
    <->
    (exists (n:nat), f n = true) \/ (exists (n:nat), g n = true).
Proof.
    intros f g. split.
    - intros [n [H1|H1]].
        + left. exists n. assumption.
        + right. exists n. assumption.
    - intros [[n H1]|[n H1]]; exists n.
        + left. assumption.
        + right. assumption.
Qed.

(* Characterises predicates p which are 'like' G in relation to f.              *)
Definition GLike (f:nat -> bool) (p:nat -> Prop) :=
    (forall (n:nat), (f n = false -> p (S n)) -> p n). 

(* The predicate 'G f' is like the predicate 'G f'.                             *)
Lemma L23 : forall (f:nat -> bool), GLike f (G f).
Proof.
    unfold GLike. intros f n H1. constructor. assumption.
Qed.

(* Similar to L5                                                                *)
Lemma L24 : forall (f:nat -> bool) (p:nat -> Prop) (n:nat), GLike f p -> 
    f n = true -> p n.
Proof.
    unfold GLike. intros f p n H1 H2. apply H1. intros H3.
    rewrite H2 in H3. inversion H3.
Qed.

(* Similar to L6                                                                *)
Lemma L25 : forall (f:nat -> bool) (p:nat -> Prop) (n:nat), GLike f p -> 
    p (S n) -> p n.
Proof.
    unfold GLike. intros f p n H1 H2. apply H1. intros H3. assumption.
Qed.

(* Similar to L7                                                                *)
Lemma L26 : forall (f:nat -> bool) (p:nat -> Prop) (n:nat), GLike f p ->
    p n -> p 0.
Proof.
    intros f p n H1. revert n. induction n as [|n IH].
    - auto.
    - intros H2. apply IH. apply L25 with f; assumption.
Qed.

(* Similar to L8                                                                *)
Lemma L27 : forall (f:nat -> bool) (p:nat -> Prop), GLike f p ->
    (exists (n:nat), f n = true) -> p 0.
Proof.
    intros f p H1 [n H2]. apply (L26 f p n H1).
    apply (L24 f p n H1). assumption.
Qed.


Lemma L28 : forall (f:nat -> bool) (n:nat),
    G f n <-> forall (p:nat -> Prop), GLike f p -> p n.
Proof.
    intros f n. split; intros H1.
    - intros p H2. revert n H1. apply elimG. assumption. 
    - apply H1. apply L23.
Qed.


Lemma L29 : forall (f:nat -> bool) (n:nat),
    G f n 
        <-> 
    forall (p:nat -> Prop), 
        (forall (n:nat), f n = true -> p n) -> 
        (forall (n:nat), p (S n) -> p n)    ->
        p n.
Proof.
    intros f n. split.
    - intros H1 p H2 H3. revert n H1. apply elimG. intros n H4. 
      destruct (f n) eqn:E.
        + apply H2. assumption.
        + apply H3, H4. reflexivity.
    - intros H1. apply H1.
        + apply L5.
        + apply L6.
Qed.

