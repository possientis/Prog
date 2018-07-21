Require Import Axiom_ProofIrrelevance.
Require Import Setoids.
Require Import Category7.
Require Import Eq_Category7.
Require Import Cast.
Require Import Eq.

Open Scope setoid.

Definition Op_Arrows_ (C:Category) := Arrows_ C.
Definition Op_source_ (C:Category) := target_ C.
Definition Op_target_ (C:Category) := source_ C.


Lemma Op_define_ : forall (C:Category) (g f: Arr C), 
    source f == target g -> target g == source f.
Proof. intros C g f. apply sym. Qed.

Definition Op_compose_(C:Category)(g f:Arr C)(p: source f == target g):Arr C := 
    compose_ C f g (Op_define_ C g f p).

Definition Op_proof_ss_ (C:Category) := proof_tt_ C.
Definition Op_proof_ts_ (C:Category) := proof_st_ C.
Definition Op_proof_tt_ (C:Category) := proof_ss_ C.
Definition Op_proof_st_ (C:Category) := proof_ts_ C.

Definition Op_proof_src_ (C:Category) : forall (f g:Arr C),
    forall (p: source f == target g), 
        target (compose_ C f g (Op_define_ C g f p)) == target f.
Proof. intros f g p.  apply proof_tgt_. Qed.

Definition Op_proof_tgt_ (C:Category) : forall (f g:Arr C),
    forall (p: source f == target g),
        source (compose_ C f g (Op_define_ C g f p)) == source g.
Proof. intros f g p. apply proof_src_. Qed.


Definition Op_proof_idl_ (C:Category) : forall (f b:Arr C),
    forall (p:source f == target b),
    b == source f -> compose_ C f b (Op_define_ C b f p) == f.
Proof. intros f b p H. apply proof_idr_. assumption. Qed.

Definition Op_proof_idr_ (C:Category) : forall (f a:Arr C),
     forall (p:source a == target f),
     a == target f -> compose_ C a f (Op_define_ C f a p) == f.
Proof. intros f a p H. apply proof_idl_. assumption. Qed.

Definition Op_proof_asc_ (C:Category) : forall (f g h:Arr C),
    forall (p_gf: source f == target g),
    forall (p_hg: source g == target h),
    forall (p_h_gf: source (compose_ C f g (Op_define_ C g f p_gf)) == target h),
    forall (p_hg_f:source f == target (compose_ C g h (Op_define_ C h g p_hg))),
    compose_ C (compose_ C f g (Op_define_ C g f p_gf)) h 
        (Op_define_ C h (compose_ C f g (Op_define_ C g f p_gf)) p_h_gf) ==
    compose_ C f (compose_ C g h (Op_define_ C h g p_hg))
        (Op_define_ C (compose_ C g h (Op_define_ C h g p_hg)) f p_hg_f).
Proof. intros f g h p_gf p_hg p_h_gf p_hg_f. apply sym. apply proof_asc_. Qed.

Definition Op_proof_compat_ (C:Category) : forall (f f' g g':Arr C),
    forall (p_gf : source f  == target g),
    forall (p_gf': source f' == target g'),
    f == f' -> g == g' -> 
    compose_ C f g (Op_define_ C g f p_gf) == 
    compose_ C f' g' (Op_define_ C g' f' p_gf').
Proof. intros f f' g g' p_gf p_gf' Hf Hg. apply proof_compat_; assumption. Qed. 

(* We are defining the opoosit category in a very unreadable way*)
Definition Op (C:Category) : Category := category
    (Op_Arrows_ C)
    (Op_source_ C)
    (Op_target_ C)
    (Op_compose_ C)
    (Op_proof_ss_ C)
    (Op_proof_ts_ C)
    (Op_proof_tt_ C)
    (Op_proof_st_ C)
    (Op_proof_src_ C)
    (Op_proof_tgt_ C)
    (Op_proof_idl_ C)
    (Op_proof_idr_ C)
    (Op_proof_asc_ C)
    (Op_proof_compat_ C)
    .
    
(* However, we are able to check this definition satifies the right properties *)

Lemma OpOp_Arr : forall (C:Category), Arr (Op (Op C)) = Arr C.
Proof. intros C. reflexivity. Qed.


Lemma OpOp_haveSameEq : forall (C:Category), haveSameEq (Op (Op C)) C.
Proof.
    intros C. unfold haveSameEq. split.
    - reflexivity.
    - intros p. split.
        + intros f g H.
          unfold Arr, Op, Op_Arrows_ in p. simpl in p.
          assert (p = eq_refl) as P. { apply proof_irrelevance. }
          rewrite P. assumption.
        + intros f g H. 
          unfold Arr, Op, Op_Arrows_ in p. simpl in p.
          assert (p = eq_refl) as P. { apply proof_irrelevance. }
          rewrite P. unfold bw, cast', eq_sym, cast. assumption.
Qed.

Lemma OpOp_Arrows_ : forall (C:Category), Arrows_ (Op (Op C)) = Arrows_ C.
Proof. intros C. apply same_Arrows_. apply OpOp_haveSameEq. Qed.

Lemma OpOp_haveSameSource : forall (C:Category), haveSameSource (Op (Op C)) C.
Proof.
    intros C. unfold haveSameSource. split.
    - apply OpOp_haveSameEq.
    - intros p f. unfold Arr, Op, Op_Arrows_ in p. simpl in p.
      assert (p = eq_refl) as P. { apply proof_irrelevance. }
      rewrite P. simpl. apply refl.
Qed.

Lemma OpOp_haveSameTarget : forall (C:Category), haveSameTarget (Op (Op C)) C.
Proof.
    intros C. unfold haveSameTarget. split.
    - apply OpOp_haveSameEq.
    - intros p f. unfold Arr, Op, Op_Arrows_ in p. simpl in p.
      assert (p = eq_refl) as P. { apply proof_irrelevance. }
      rewrite P. simpl. apply refl.
Qed.


Lemma OpOp_haveSameCompose : forall (C:Category), haveSameCompose (Op (Op C)) C.
Proof.
    intros C. unfold haveSameCompose. split.
    - apply OpOp_haveSameSource.
    - split.
        + apply OpOp_haveSameTarget.
        + intros p S T f g H H'.
          unfold Arr, Op, Op_Arrows_ in p. simpl in p.
          assert (p = eq_refl) as P. { apply proof_irrelevance. }
          revert H'. rewrite P. simpl. intros H'.
          unfold Op_compose_, compose.
          assert (Op_define_ C f g (Op_define_ (Op C) g f H) = H') as E.
            { apply proof_irrelevance. }
          rewrite E. apply refl.
Qed.

Theorem Op_involutive : forall (C:Category), catEq (Op (Op C)) C.
Proof. intros C. unfold catEq. apply OpOp_haveSameCompose. Qed.

