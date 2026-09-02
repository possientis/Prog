Require Import nat.
Require Import list.
Require Import dictionary.
Require Import syntax.
Require Import state.
Require Import execute.
Require Import eval.
Require Import ISA.

Fixpoint s_compile (a:aexp) : list sinstr :=
  match a with
  | ANum n        => [SPush n]
  | AKey k        => [SLoad k]
  | APlus  a1 a2  => (s_compile a1) ++ (s_compile a2) ++ [SPlus]
  | AMinus a1 a2  => (s_compile a1) ++ (s_compile a2) ++ [SMinus]
  | AMult  a1 a2  => (s_compile a1) ++ (s_compile a2) ++ [SMult]
  end.

Lemma compile_correct_help : forall (e:State) (a:aexp) (stack: list nat),
  s_execute e stack (s_compile a) = (aeval e a) :: stack.
Proof.
  intros e a. revert e. 
  induction a as [n|k|a1 IH1 a2 IH2|a1 IH1 a2 IH2|a1 IH1 a2 IH2].
  - intros e stack. simpl. reflexivity.
  - intros e stack. simpl. reflexivity.
  - intros e stack. simpl. 
      rewrite s_execute_app, s_execute_app, IH1, IH2. reflexivity.
  - intros e stack. simpl. 
      rewrite s_execute_app, s_execute_app, IH1, IH2. reflexivity.
  - intros e stack. simpl. 
      rewrite s_execute_app, s_execute_app, IH1, IH2. reflexivity.
Qed.

Theorem compile_correct : forall (e:State) (a:aexp),
  s_execute e [] (s_compile a) = [aeval e a].
Proof. intros e a. apply compile_correct_help. Qed.



