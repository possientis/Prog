Require Import List.

Require Import CpdtTactics.

Set Implicit Arguments.
(*Set Asymmetric Patterns.*)


Print unit.
Print True.

Section Propositional.
  Variables P Q R : Prop.

  Theorem obvious : True.
    apply I.
  Qed.

  Theorem obvious' : True.
    constructor.
  Qed.

  Print False.


  Theorem False_imp : False -> 2 + 2 = 5.
    destruct 1. (* case analysis *)
  Qed.

  Theorem arith_neq : 2 + 2 = 5 -> 9 + 9 = 835.
    intro.
    elimtype False.
    crush. (* how do we do it manually ? *)
  Qed.  


    Print not.

  Theorem arith_neq' : ~ (2 + 2 = 5).
    unfold not.
    crush.
  Qed.


  Print and.



  Theorem and_comm : P /\ Q -> Q /\ P.
    intro.
    destruct H.
    split.
    assumption.
    assumption.
  Qed.


  Print or.



  Theorem or_comm : P \/ Q -> Q \/ P.
    destruct 1.
    right.
    assumption.
    left.
    assumption.
  Qed.

  

  Theorem or_comm' : P \/ Q -> Q \/ P.
    tauto.
  Qed.

  
  Theorem arith_comm : forall ls1 ls2 : list nat,
    length ls1 = length ls2 \/ length ls1 + length ls2 = 6
    -> length (ls1 ++ ls2) = 6 \/ length ls1 = length ls2.

    intuition.
    rewrite app_length.
    tauto.
  Qed.

  Theorem arith_comm' : forall ls1 ls2 : list nat,
    length ls1 = length ls2 \/ length ls1 + length ls2 = 6
    -> length (ls1 ++ ls2) = 6 \/ length ls1 = length ls2.
    Hint Rewrite app_length.
    crush.
  Qed.

End Propositional. (* all our proved theorems become universally quantified
over the propositional variables that we used *)



  


  





