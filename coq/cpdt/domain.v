Require Import extensionality.
Require Import irrelevance.
Require Import Nat.
Require Import Max2.

(********************************************************************************)
(************************* Parial Order on 'option a' ***************************)
(********************************************************************************)

Definition ole (a:Type) (x y:option a) : Prop :=
    forall (v:a), x = Some v -> y = Some v.

Arguments ole {a} _ _.

Lemma ole_refl : forall (a:Type) (x:option a), ole x x.
Proof. intros a x v H. assumption. Qed.

Lemma ole_anti : forall (a:Type) (x y:option a),
    ole x y -> ole y x -> x = y.
Proof.
    unfold ole. intros a x y Hxy Hyx. destruct x as [v|], y as [w|].
        - apply Hyx. reflexivity.
        - symmetry. apply Hxy. reflexivity.
        - apply Hyx. reflexivity.
        - reflexivity.
Qed.

Lemma ole_trans : forall (a:Type) (x y z:option a),
    ole x y -> ole y z -> ole x z.
Proof.
    unfold ole. intros a x y z Hxy Hyz v H.
    apply Hyz, Hxy. assumption.
Qed.

Definition ole' (a:Type) (x y:option a) : Prop :=
    match x with
    | None          => True
    | Some v        =>
        match y with
        | None      => False
        | Some w    => v = w
        end
    end.

Arguments ole' {a} _ _.

Lemma ole_equivalence : forall (a:Type) (x y:option a),
    ole x y <-> ole' x y.
Proof.
    intros a x y. unfold ole, ole'. destruct x as [v|], y as [w|]; split.    
    - intros H. assert (Some w = Some v) as E.
        { apply H. reflexivity. }
        inversion E. reflexivity.
    - intros H1. subst. intros v H. assumption.
    - intros H. assert (None = Some v) as E.
        { apply H. reflexivity. }
        inversion E.
    - intros H1. exfalso. assumption.
    - intros H. apply I.
    - intros H1 v H2. inversion H2.
    - intros H. apply I.
    - intros H1 v H2. assumption.
Qed.


(********************************************************************************)
(******************************* Monotone Maps **********************************)
(********************************************************************************)

(* Bad definition from cpdt                                                     *)
Definition monotone (a:Type) (f:nat -> option a) : Prop :=
    forall (n:nat) (v:a), f n = Some v -> 
    forall (m:nat), n <= m -> f m = Some v.

Arguments monotone {a} _.


(* Checking bad definition makes sense                                          *)
Lemma monotone_check : forall (a:Type) (f:nat -> option a),
    monotone f <-> forall (n m:nat), n <= m -> ole (f n) (f m).
Proof.
    intros a f. split; unfold monotone, ole; intros H.
    - intros n m H1 v H2. apply H with n; assumption.
    - intros n v H1 m H2. apply H with n; assumption.
Qed.



(********************************************************************************)
(******************************** Computations **********************************)
(********************************************************************************)


(* A computation is a monotone map                                              *)
Definition Computation (a:Type) : Type := { f:nat -> option a | monotone f }.

Definition eval (a:Type) (c:Computation a) (n:nat) : option a := proj1_sig c n.

Arguments eval {a}.

(* Expresses the fact that computation k yields value v for input n             *)
Definition runTo (a:Type) (k:Computation a) (n:nat) (v:a) : Prop :=
    eval k n = Some v.

Arguments runTo {a} _ _ _.

(* Expresses the fact that computation k eventually yields v                    *) 
Definition run (a:Type) (k:Computation a) (v:a) : Prop :=
    exists (n:nat), runTo k n v.

Arguments run {a} _ _.

(* We are defining a value with coq tactics. This value is essentially a tuple  *)
(* where the second coordinate is a proof, so using tactics appears to be       *)
(* making sense. Note that this proof is not opaque ('Defined' rather than      *)
(* 'Qed'). Alternatively, we could have defined the proof separately as some    *)
(* sort of lemma and defined the value 'bot' in the usual direct way by         *)
(* referring to this lemma                                                      *)

Definition bot' (a:Type) : Computation a.
    unfold Computation. exists (fun (_:nat) => None).
    unfold monotone. intros n v H. inversion H.
Defined.

Arguments bot' {a}.


Definition botf (a:Type) (n:nat) : option a := None.

Arguments botf {a} _.

Lemma botp : forall (a:Type), monotone (@botf a).
Proof.
    unfold monotone, botf. intros a n v H. inversion H.
Qed.

Arguments botp {a}.

(* A lot better I think, details of proof decoupled from computation logic      *)
Definition bot (a:Type) : Computation a :=
    exist monotone botf botp.

Arguments bot {a}.

(********************************************************************************)
(************************ Equality between Computations *************************)
(********************************************************************************)

Definition ceq (a:Type) (k1 k2:Computation a) : Prop :=
    forall (n:nat), eval k1 n = eval k2 n.

Arguments ceq {a} _ _.

Notation "x == y" := (ceq x y) (at level 90).

Lemma ceq_refl : forall (a:Type) (x:Computation a), x == x.
Proof.
    intros a [f p] n. simpl. reflexivity.
Qed.

Lemma ceq_sym  : forall (a:Type) (x y:Computation a), 
    x == y -> y == x.
Proof.
    intros a [f p] [g q] H n. simpl. symmetry. apply H.
Qed.

Lemma ceq_trans : forall (a:Type) (x y z:Computation a),
    x == y -> y == z -> x == z.
Proof.
    intros a [f p] [g q] [h r] Hxy Hyz n. simpl.
    apply eq_trans with (g n).
    - apply Hxy.
    - apply Hyz.
Qed.


(********************************************************************************)
(**************************** Computation as Monad ******************************)
(********************************************************************************)

(* 'return' is a keyword in coq, so using 'pure' instead                        *)
Definition pure' (a:Type) : a -> Computation a.
    intros v. 
    unfold Computation. exists (fun (_:nat) => Some v).
    unfold monotone. intros n w H. inversion H. subst.
    intros m H'. reflexivity.
Defined.

Arguments pure' {a} _.

(* computation is made explicit                                                 *)
Definition puref (a:Type)(x:a)(n:nat) : option a := Some x.

Arguments puref {a} _ _.

(* statement of what it is we are proving is also clear                         *)
Lemma purep : forall (a:Type) (x:a), monotone (puref x).
Proof.
    unfold monotone, puref. intros a x n v H m H'. 
    inversion H. subst. reflexivity.
Qed.

Arguments purep {a} _.

(* wrapping up in a single function, no complexity here                         *)
Definition pure (a:Type)(x:a) : Computation a :=
    exist monotone (puref x) (purep x).

Arguments pure {a} _.

(* Checking 'pure' has the intended semantics                                   *)
Lemma run_pure : forall (a:Type) (v:a), run (pure v) v. 
Proof.
    intros a v. unfold run. exists 0. reflexivity.
Qed.


(* Totally useless definition. computation logic and proof are coupled          *)
Definition bind'(a b:Type)(k:Computation a)(g:a -> Computation b):Computation b.
    unfold Computation. 
    remember (fun (n:nat) =>
        match eval k n with
        |   Some va => proj1_sig (g va) n
        |   None    => None
        end) as gf eqn:GF.
    exists gf.
    unfold monotone. 
    intros n vb H m I.
    destruct k as [f Mf]. simpl in GF. 
    unfold monotone in Mf.
    rewrite GF in H. rewrite GF.
    destruct (f n) as [va|] eqn:Fn.
        - destruct (f m) as [va'|] eqn:Fm.
            + assert (f m = Some va) as E. 
                { apply Mf with n; assumption. }
              rewrite Fm in E. inversion E.
              destruct (g va) as [g' Mg']. simpl. simpl in H.
              unfold monotone in Mg'. apply Mg' with n; assumption.
            + assert (f m = Some va) as E.
                { apply Mf with n; assumption. }
              rewrite Fm in E. inversion E.
        - inversion H.
Defined.


Arguments bind' {a} {b} _ _.

(* computation logic of bind is plainly visible                                 *) 
Definition bindf 
    (a b:Type)
    (k:Computation a)
    (g:a -> Computation b)
    (n:nat)
    :option b :=
    match k with                    (* unpack computation k             *) 
    | exist _ f _ =>
        match (f n) with            (* result of f after n cycles       *) 
        | None   => None            (* first computation fails          *)
        | Some v =>                 (* first computation returns value  *)
            match (g v) with        (* unpack second computation        *)
            | exist _ h _ => h n    (* returns result after n cycles    *)
            end
        end
    end.

Arguments bindf {a} {b} _ _ _.

(* what we are proving is clear                                                 *)
Lemma bindp : forall (a b:Type) (k:Computation a) (g:a -> Computation b),
    monotone (bindf k g).
Proof.
    unfold monotone, bindf. intros a b [f p] g n v H m H'.
    destruct (f n) as [x|] eqn:E.
    - unfold monotone in p. rewrite (p n x).
        + destruct (g x) as [h q]. unfold monotone in q. 
          apply q with n; assumption.
        + assumption.
        + assumption.
    - inversion H.
Qed.

Arguments bindp {a} {b} _ _.

(* packing adds no complexity                                                   *)
Definition bind (a b:Type) (k:Computation a) (g:a -> Computation b) 
    : Computation b := exist monotone (bindf k g) (bindp k g).

Arguments bind {a} {b}.

Notation "k >>= g" := (bind k g) (at level 50, left associativity).

(* checking bind has the intended semantics                                      *)
Lemma run_bind : forall (a b:Type) (k:Computation a) (h:a -> Computation b),
    forall (x:a) (y:b), run k x -> run (h x) y -> run (k >>= h) y.
Proof.
    intros a b [f p] h x y [n Hx] [m Hy].
    destruct (h x) as [g q] eqn:H.
    unfold runTo in Hx. simpl in Hx.
    unfold runTo in Hy. simpl in Hy.
    unfold monotone in p. unfold monotone in q.
    unfold run. unfold runTo.
    exists (max n m). unfold bind. simpl.
    assert (f (max n m) = Some x) as E. 
        { apply p with n. assumption. apply n_le_max. }
    rewrite E, H. simpl. apply q with m. 
        - assumption.
        - apply m_le_max.
Qed.


(********************************************************************************)
(************************** Checking Monad Laws *********************************)
(********************************************************************************)

Lemma left_identity : forall (a b:Type) (x:a) (h:a -> Computation b),
    (pure x) >>= h == h x.
Proof. intros a b x h n. simpl. destruct (h x) as [f p]. reflexivity. Qed. 

Lemma right_identity : forall (a:Type) (k:Computation a), 
    k >>= pure == k.
Proof. intros a [f p] n. simpl. destruct (f n) as [v|]; reflexivity. Qed. 

Lemma associativity : forall (a b c:Type), 
    forall (k:Computation a) (f:a -> Computation b) (g:b -> Computation c),
    k >>= f >>= g == k >>= (fun (x:a) => (f x) >>= g).
Proof.
    intros a b c [k p] f g n. simpl. destruct (k n) as [v|].
    - destruct (f v) as [h q]. reflexivity.
    - reflexivity.
Qed.

(********************************************************************************)
(********************** Partial Order on Computations  **************************)
(********************************************************************************)

Definition cle (a:Type) (x y:Computation a) : Prop :=
    forall (n:nat), ole (eval x n) (eval y n).

Arguments cle {a} _ _.

Lemma cle_refl : forall (a:Type) (x:Computation a), cle x x.
Proof. intros a [f p] n. apply ole_refl. Qed.

(* Assuming extensionality and proof irrelevance                                *)
Lemma cle_anti : forall (a:Type) (x y:Computation a),
    cle x y -> cle y x -> x = y.
Proof.
    unfold cle. intros a [f p] [g q]. simpl. intros H1 H2.
    assert (f = g) as H.
        { apply extensionality. intros n. apply ole_anti.
          - apply H1. 
          - apply H2.
        }
    clear H1 H2. revert p q. subst. intros p q.
    assert (p = q) as H. { apply irrelevance. } subst.
    reflexivity.
Qed.

Lemma cle_trans : forall (a:Type) (x y z:Computation a), 
    cle x y -> cle y z -> cle x z.
Proof.
    unfold cle. intros a [f p] [g q] [h r]. simpl. intros H1 H2 n.
    apply ole_trans with (g n).
        - apply H1.
        - apply H2.
Qed.

Definition cle' (a:Type) (x y:Computation a) : Prop :=
    forall (n:nat) (v:a), runTo x n v -> runTo y n v.

Arguments cle' {a} _ _.
 
Lemma cle_equivalence: forall (a:Type) (x y:Computation a),
    cle x y <-> cle' x y.
Proof.
    unfold cle, cle', ole, runTo. intros a x y. split; intros H; assumption.
Qed.


(********************************************************************************)
(************** Partial Order on Arrows 'a -> Computation b'  *******************)
(********************************************************************************)

Definition cfle (a b:Type) (f g:a -> Computation b) : Prop :=
    forall (x:a), cle (f x) (g x).

Arguments cfle {a} {b} _ _.

Lemma cfle_refl : forall (a b:Type) (f:a -> Computation b), cfle f f.
Proof.
    unfold cfle. intros a b f x. apply cle_refl.
Qed.

Lemma cfle_anti : forall (a b:Type) (f g:a -> Computation b),
    cfle f g -> cfle g f -> f = g.
Proof.
    unfold cfle. intros a b f g H1 H2. apply extensionality.
    intros x. apply cle_anti.
        - apply H1.
        - apply H2.
Qed.

Lemma cfle_trans : forall (a b:Type) (f g h:a -> Computation b),
    cfle f g -> cfle g h -> cfle f h.
Proof.
    unfold cfle. intros a b f g h H1 H2 x.
    apply cle_trans with (g x).
        - apply H1.
        - apply H2.
Qed.

(* 'slice at n', just a preorder though                                         *)
Definition cfle_n (a b:Type) (n:nat) (f g:a -> Computation b) : Prop :=
    forall (x:a), ole (eval (f x) n) (eval (g x) n).

Arguments cfle_n {a} {b}.
    
Lemma cfle_n_refl : forall (a b:Type) (n:nat) (f:a -> Computation b),
    cfle_n n f f.
Proof. intros a b n f x. apply ole_refl. Qed.


Lemma cfle_n_trans : forall (a b:Type) (n:nat) (f g h:a -> Computation b),
    cfle_n n f g -> cfle_n n g h -> cfle_n n f h.
Proof.
    intros a b n f g h H1 H2 x. apply ole_trans with (eval (g x) n).
        - apply H1.
        - apply H2.
Qed.

(********************************************************************************)
(************************* Continuous Function on Arrows  ***********************)
(********************************************************************************)

Definition continuous (a b: Type)(F:(a -> Computation b)->(a -> Computation b)):=
    forall (f g:a -> Computation b)(n:nat), 
        cfle_n n f g  -> cfle_n n (F f) (F g). 

Arguments continuous {a} {b}.

(* This is a stronger property than just being monotone wr to cfle              *)

Lemma continuous_stronger : forall (a b:Type) 
    (F:(a -> Computation b)->(a -> Computation b)), continuous F ->
        forall (f g:a -> Computation b), cfle f g -> cfle (F f) (F g).
Proof.
    intros a b F C f g H x n. revert x. apply C. intros x. apply H. 
Qed.

Definition Operator (a b:Type) : Type := 
    {F: (a -> Computation b) -> (a -> Computation b) | continuous F}.


Definition ap (a b:Type) (F:Operator a b) (f:a -> Computation b)
    : a -> Computation b := proj1_sig F f.

Arguments ap {a} {b}.

Notation "F $ f" :=(ap F f) (at level 60, right associativity).

(********************************************************************************)
(************************ The Fixed Point of an Operator  ***********************)
(********************************************************************************)

Definition init (a b:Type) : a -> Computation b := (fun x => bot).

Arguments init {a} {b}.

Fixpoint iter (a b:Type) (F:Operator a b) (n:nat) : a -> Computation b :=
    match n with
    | 0     => init
    | S n   => F $ (iter a b F n)
    end.

Arguments iter {a} {b}.

Lemma iter_increasing_ : forall (a b:Type) (F:Operator a b) (n:nat),
    cfle (iter F n) (iter F (S n)).
Proof.
    intros a b [F p]. induction n as [|n IH].
    - unfold cfle, iter, cle, init, ole, bot, ap, botf.
      simpl. intros x n v H. inversion H.
    - intros x m. simpl. revert x. apply p. intros x. apply IH.
Qed.

Lemma iter_increasing : forall (a b:Type) (F:Operator a b) (n m:nat),
    n <= m -> cfle (iter F n) (iter F m).
Proof.
    intros a b F n m H. induction H as [|m H IH].
    - apply cfle_refl.
    - apply cfle_trans with (iter F m).
        + assumption.
        + apply iter_increasing_.
Qed.

Definition Fixf (a b:Type) (F:Operator a b) (x:a) (n:nat) : option b :=
    eval (iter F n x) n.  

Arguments Fixf {a} {b}.

Lemma Fixp : forall (a b:Type) (F:Operator a b) (x:a), monotone (Fixf F x).
Proof.
    intros a b F x. apply monotone_check. intros n m H.
    unfold Fixf. apply ole_trans with (proj1_sig (iter F n x) m).
    - destruct (iter F n x) as [f p]. simpl. apply monotone_check; assumption.
    - apply iter_increasing. assumption.
Qed.

Arguments Fixp {a} {b}.


Definition Fix (a b:Type) (F:Operator a b) (x:a) : Computation b :=
    exist monotone (Fixf F x) (Fixp F x).

Arguments Fix {a} {b}.

(* key lemma                                                                    *)
Lemma FFix_iter : forall (a b:Type) (F:Operator a b) (x:a) (n:nat),
    eval ((F $ Fix F) x) n = eval (iter F (S n) x) n.
Proof.
    intros a b F x n. 
    destruct F as [F' p] eqn:E. rewrite <- E.
    unfold continuous, cfle_n in p.
    remember (Fix F) as f eqn:E1.
    remember (iter F n) as g eqn:E2.
    assert (eval (F' f x) n = eval ((F $ f) x) n) as E3. 
        { unfold eval, ap. rewrite E. reflexivity. }
    assert (eval (F' g x) n = eval (iter F (S n) x) n) as E4.
        { unfold eval. rewrite E2. unfold iter, ap. rewrite E. reflexivity. }
    assert (forall (x:a), eval (f x) n = eval (g x) n) as H.
        { intros y. rewrite E1, E2. unfold Fix,Fixf, iter, eval. reflexivity. }
    rewrite <- E3, <- E4.
    apply ole_anti; apply p; intros y; rewrite H; apply ole_refl.
Qed.

(* If computation F (Fix F) terminates @x, so will computation Fix F @x         *)
Lemma FFix_Fix : forall (a b:Type) (F:Operator a b) (x:a) (n:nat),
    ole (eval ((F $ Fix F) x) n) (eval (Fix F x) (S n)).
Proof.
    intros a b F x n. apply ole_trans with (eval (iter F (S n) x) n).
    - rewrite FFix_iter. apply ole_refl.
    - assert (eval (Fix F x) (S n) = eval (iter F (S n) x) (S n)) as E.
        { reflexivity. }
      rewrite E. destruct (iter F (S n) x) as [f p]. simpl.
      apply monotone_check. 
        + assumption.
        + apply le_S, le_n.
Qed.

(* If computation Fix F terminates @x, so will computation F (Fix F) @x         *)
Lemma Fix_FFix : forall (a b:Type) (F:Operator a b) (x:a) (n:nat),
    ole (eval (Fix F x) n) (eval ((F $ Fix F) x) n).
Proof.
    intros a b F x n. rewrite FFix_iter. apply iter_increasing_.
Qed.


(* checking Fix has the intended semantics  *)
(* F (Fix F) terminates iff (Fix F) terminates, and both results equal          *)
Theorem run_Fix : forall (a b:Type) (F:Operator a b) (x:a) (v:b),
    run ((F $ Fix F) x) v <-> run (Fix F x) v.
Proof.
    intros a b F x v. split; unfold run, runTo; intros [n H].
    - exists (S n). apply FFix_Fix. assumption.
    - exists n. apply Fix_FFix. assumption.
Qed.


