Require Import Logic.Class.Eq.
Require Import Logic.Prop.Syntax.

(* If equality on v is decidable, then so is equality on P v                    *)
Lemma eqDecidable : forall (v:Type) (e:Eq v),
  forall (p q:P v), {p = q} + {p <> q}.
Proof.
  (* Let v be a type and e be a decidable equality on v *)
  intros v e.

  (* Proof by induction on p *)
  induction p as [|x|p1 IH1 p2 IH2].

    (* case when p = Bot, case analysis on q *)
    - destruct q as [|y|q1 q2].

      (* case q = Bot, we have equality *)
      + left. reflexivity.

      (* case q = Var y, p and q are not equal *)
      + right. intro A. inversion A.

      (* case q = q1 :-> q2, p and q are not equal *)
      + right. intro A. inversion A.

    (* case when p = Var x, case analysis on q *)
    - destruct q as [|y|q1 q2].

      (* case q = Bot, p and q are not equal *)
      + right. intro A. inversion A.

      (* case q = Var y, we need to distinguish between x = y and x <> y *)
      + destruct (eqDec x y) as [Hxy|Hxy].

        (* case when x = y, p and q are equal *)
        * left. rewrite Hxy. reflexivity.

        (* case when x <> y, p and q are not equal *)
        * right. intro A. inversion A. contradiction.

      (* case q = q1 :-> q2, p and q are not equal *)
      + right. intro A. inversion A.
      
    (* case when p = p1 p2, case analysis on q *)
    - destruct q as [|y|q1 q2].

      (* case when q = Bot, p and q are not equal *)
      + right. intro A. inversion A.

      (* case when q = var x, p and q are not equal *)
      + right. intro A. inversion A.

      (* case when q = q1 :-> q2, check whether p1 = q1 and p2 = q2 *)
      + destruct (IH1 q1) as [H1|H1], (IH2 q2) as [H2|H2].

        (* case when p1 = q1 and p2 = q2, p and q are equal *)
        * left. rewrite H1, H2. reflexivity.

        (* case when p1 = q1 but p2 <> q2, p and q are not equal *)
        * right. intro A. inversion A. contradiction.

        (* case when p1 <> q1 and p2 = q2. p and q are not equal *)
        * right. intro A. inversion A. contradiction.

        (* case when p1 <> q1 and p2 <> q2, p and q are not equal *)
        * right. intro A. inversion A. contradiction.
Defined.

Arguments eqDecidable {v} {e}.

Global Instance EqP (v:Type) (e:Eq v) : Eq (P v) := { eqDec := eqDecidable }.

