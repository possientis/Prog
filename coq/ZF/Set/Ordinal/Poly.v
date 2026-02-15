Require Import ZF.Class.Equiv.
Require Import ZF.Class.Ordinal.ShiftL.
Require Import ZF.Class.Ordinal.ShiftR.
Require Import ZF.Class.Relation.ToFun.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Decreasing.
Require Import ZF.Set.Ordinal.Exp.
Require Import ZF.Set.Ordinal.Limit.
Require Import ZF.Set.Ordinal.Mult.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.Ordinal.Omega.
Require Import ZF.Set.Ordinal.OrdFun.
Require Import ZF.Set.Ordinal.OrdFunOn.
Require Import ZF.Set.Ordinal.Plus.
Require Import ZF.Set.Ordinal.ShiftL.
Require Import ZF.Set.Ordinal.ShiftR.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Ordinal.SumOfClass.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.Functional.
Require Import ZF.Set.Single.

Require Import ZF.Notation.Eval.

Module COL := ZF.Class.Ordinal.ShiftL.
Module COR := ZF.Class.Ordinal.ShiftR.
Module SOL := ZF.Set.Ordinal.ShiftL.
Module SOR := ZF.Set.Ordinal.ShiftR.

Proposition IsElem : forall (a b c d n:U),
  Ordinal a                                             ->
  Ordinal d                                             ->
  n :< :N                                               ->
  OrdFunOn b n                                          ->
  OrdFunOn c n                                          ->
  Decreasing b                                          ->
  :1: :< a                                              ->
  (forall i, i :< n -> b!i :< d)                        ->
  (forall i, i :< n -> c!i :< a)                        ->
  :sum:_{n} (:[fun i => a :^: b!i :*: c!i]:) :< a :^: d.
Proof.
  intros a b c d n H1 H2 H3 H4 H5 H6 H7.
  revert n H3 b c d H2 H4 H5 H6.
  assert (Ordinal :0:) as G1. { apply Core.ZeroIsOrdinal. }
  assert (Ordinal :1:) as G2. { apply Natural.OneIsOrdinal. }
  assert (:0: :< a) as G3. {
    apply Core.ElemElemTran with :1:; try assumption.
    apply Succ.IsIn. }
  remember (fun n =>
    forall b c d: U,
    Ordinal d ->
    OrdFunOn b n ->
    OrdFunOn c n ->
    Decreasing b ->
    (forall i, i :< n -> b!i :< d) ->
    (forall i, i :< n -> c!i :< a) ->
    :sum:_{ n} (:[ fun i => a :^: b!i :*: c!i ]:) :< a :^: d)
    as A eqn:H8.
  assert (forall n, n :< :N -> A n) as H9. {
    apply Omega.Induction; rewrite H8.
    - intros b c d  H2 _ _ _ _ _.
      rewrite SumOfClass.WhenZero. apply Exp.HasZero; assumption.
    - intros n H3 IH b c d H2 H4 H5 H6 H9 H10.
      assert (Ordinal n) as G4. { apply Omega.HasOrdinalElem. assumption. }
      assert (Functional b) as G5. { apply H4. }
      assert (Functional c) as G6. { apply H5. }
      assert (domain b = succ n) as G7. { apply H4. }
      assert (domain c = succ n) as G8. { apply H5. }
      remember (fun i => a :^: b!i :*: c!i) as F eqn:E.
      assert (CRL.Functional :[F]:) as H11. { apply ToFun.IsFunctional. }
      assert (forall i, i :< succ n -> CRD.domain :[F]: i) as H12. {
          intros i _. apply ToFun.DomainOf. }
      assert (forall i, i :< succ n -> Ordinal b!i) as H13. {
        intros i H13. apply OrdFunOn.IsOrdinal with (succ n); assumption. }
      assert (forall i, i :< succ n -> Ordinal c!i) as H14. {
        intros i H14. apply OrdFunOn.IsOrdinal with (succ n); assumption. }
      assert (forall i : U, i :< succ n -> Ordinal (:[F]:!i)) as H15. {
          intros i H15. rewrite ToFun.Eval. rewrite E.
          apply Mult.IsOrdinal.
          - apply Exp.IsOrdinal. 1: assumption. apply H13. assumption.
          - apply H14. assumption. }
      rewrite SumOfClass.ShiftL, ToFun.Eval; try assumption.
      remember (shiftL b) as b' eqn:H16.
      remember (shiftL c) as c' eqn:H17.
      assert (OrdFunOn b' n) as H18. {
        rewrite H16. apply SOL.OnSucc. assumption. }
      assert (OrdFunOn c' n) as H19. {
        rewrite H17. apply SOL.OnSucc. assumption. }
      assert (Decreasing b') as H20. {
        rewrite H16. apply SOL.IsDecreasing. 2: assumption. apply H4. }
      assert (Ordinal b!:0:) as H21. {
        apply OrdFunOn.IsOrdinal with (succ n). 1: assumption.
        apply Succ.HasZero. assumption. }
      assert (forall i, i :< n -> c'!i :< a) as H22. {
        intros i H22.
        assert (Ordinal i) as G9. { apply Core.IsOrdinal with n; assumption. }
        rewrite H17, SOL.Eval. 2: assumption.
        - apply H10, Succ.ElemCompat; assumption.
        - rewrite G8. apply Succ.ElemCompat; assumption. }
      assert (forall i, i :< n -> b'!i :< b!:0:) as H23. {
        intros i H23.
        assert (Ordinal i) as G9. { apply Core.IsOrdinal with n; assumption. }
        rewrite H16, SOL.Eval. 2: assumption.
        - apply H6.
          + rewrite G7. apply Succ.HasZero. assumption.
          + rewrite G7. apply Succ.ElemCompat; assumption.
          + apply Succ.HasZero. assumption.
        - rewrite G7. apply Succ.ElemCompat; assumption. }
      remember (fun i => a :^: b'!i :*: c'!i) as G eqn:E'.
      assert (:sum:_{n} (COL.shiftL :[F]:) = :sum:_{n} :[G]:) as H24. {
        apply SumOfClass.EqualCharac. 1: assumption.
        intros i H24.
       assert (Ordinal i) as G9. { apply Core.IsOrdinal with n; assumption. }
        rewrite
          COL.Eval, ToFun.Eval, ToFun.Eval, E, E', H16, H17, SOL.Eval, SOL.Eval;
        try assumption. 1: reflexivity.
        - rewrite G8. apply Succ.ElemCompat; assumption.
        - rewrite G7. apply Succ.ElemCompat; assumption.
        - apply ToFun.DomainOf. }
      assert ((:sum:_{n} :[G]:) :< a :^: b!:0:) as H25. {
        rewrite E'. apply IH; assumption. }
      rewrite H24.
      assert (Ordinal (a :^: d)) as G9. { apply Exp.IsOrdinal; assumption. }
      assert (Ordinal (a :^: b!:0:)) as G10. { apply Exp.IsOrdinal; assumption. }
      assert (Ordinal (F :0:)) as G11. {
        rewrite E. apply Mult.IsOrdinal. 1: assumption.
        apply H14, Succ.HasZero. assumption. }
      assert (forall i, i :< n -> Ordinal b'!i) as G12. {
        intros i G12. apply Core.IsOrdinal with b!:0:. 1: assumption.
        apply H23. assumption. }
      assert (forall i, i :< n -> Ordinal c'!i) as G13. {
        intros i G13. apply Core.IsOrdinal with a. 1: assumption.
        apply H22. assumption. }
      assert (forall i, i :< n -> Ordinal (a :^: b'!i)) as G14. {
        intros i G14. apply Exp.IsOrdinal. 1: assumption.
        apply G12. assumption. }
      assert (forall i, i :< n -> Ordinal (G i)) as G15. {
        rewrite E'. intros i G15. apply Mult.IsOrdinal.
        - apply G14. assumption.
        - apply G13. assumption. }
      assert (Ordinal (:sum:_{n} :[G]:)) as G16. {
        apply SumOfClass.IsOrdinal. 1: assumption.
        intros i G16. rewrite ToFun.Eval. apply G15. assumption. }
      assert (Ordinal (F :0: :+: :sum:_{n} :[G]:)) as G17. {
        apply Plus.IsOrdinal; assumption. }
      assert (Ordinal (F :0: :+: a :^: b!:0:)) as G18. {
        apply Plus.IsOrdinal; assumption. }
      apply Core.ElemInclTran with (F :0: :+: a :^: b!:0:); try assumption.
      + apply Plus.ElemCompatR; assumption.
      + rewrite E.
        assert (
          a :^: b!:0: :*: (c!:0: :+: :1:)
        = a :^: b!:0: :*: c!:0: :+: a :^: b!:0:) as H26. {
          rewrite Mult.DistribL, Mult.WhenOneR; try assumption. 1: reflexivity.
          apply H14, Succ.HasZero. assumption. }
        rewrite <- H26, Plus.WhenOneR.
        assert (succ c!:0: :<=: a) as H27. {
          apply Succ.ElemIsIncl. 2: assumption.
          - apply H14, Succ.HasZero. assumption.
          - apply H10, Succ.HasZero. assumption. }
        assert (Ordinal (succ c!:0:)) as G19. {
          apply Succ.IsOrdinal. apply H14, Succ.HasZero. assumption. }
        apply Incl.Tran with (a :^: b!:0: :*: a).
        * apply Mult.InclCompatR; assumption.
        * rewrite <- Exp.WhenSuccR. 2: assumption.
          assert (Ordinal (succ b!:0:)) as G20. {
            apply Succ.IsOrdinal. assumption. }
          assert (succ b!:0: :<=: d) as H28. {
            apply Succ.ElemIsIncl; try assumption.
            apply H9, Succ.HasZero. assumption. }
          apply Exp.InclCompatR; assumption. }
  rewrite H8 in H9. assumption.
Qed.

Proposition  IsElemNat : forall (a b m n:U),
  Limit a                                                ->
  n :< :N                                                ->
  OrdFunOn b (succ n)                                    ->
  OrdFunOn m (succ n)                                    ->
  Decreasing b                                           ->
  (forall i, i :< succ n -> m!i :< :N)                   ->
  :sum:_{succ n} (:[fun i => a :^: b!i :*: m!i]:)        :<
  a :^: b!:0: :*: succ m!:0:.
Proof.
  intros a b m n H1 H2 H3 H4 H5 H7.
  remember (fun i => a :^: b!i :*: m!i) as F eqn:H10.
  remember (:sum:_{succ n} :[F]:) as s eqn:H11.
  assert (Ordinal a) as G0. { apply H1. }
  assert (forall i, i :< succ n -> Ordinal b!i) as G1. {
    intros i G1. apply OrdFunOn.IsOrdinal with (succ n); assumption. }
  assert (forall i, i :< succ n -> Ordinal m!i) as G2. {
    intros i G2. apply OrdFunOn.IsOrdinal with (succ n); assumption. }
  assert (Ordinal n) as G3. { apply Omega.HasOrdinalElem. assumption. }
  assert (succ n :< :N) as G4. { apply Omega.HasSucc. assumption. }
  assert (:0: :< succ n) as G5. { apply Omega.SuccHasZero. assumption. }
  assert (forall i, i :< succ n -> Ordinal (:[F]:!i)) as G6. {
    intros i G6. rewrite ToFun.Eval, H10.
    apply Mult.IsOrdinal.
    - apply Exp.IsOrdinal. 1: assumption. apply G1. assumption.
    - apply G2. assumption. }
  assert (domain b = succ n) as G7. { apply H3. }
  assert (domain m = succ n) as G8. { apply H4. }
  assert (Ordinal (succ n)) as G10. { apply Succ.IsOrdinal. assumption. }
  assert (Ordinal s) as G11. {
    rewrite H11. apply SumOfClass.IsOrdinal. 1: assumption.
    intros i G11. apply G6. assumption. }
  assert (Ordinal b!:0:) as G12. { apply G1. assumption. }
  assert (Ordinal (succ b!:0:)) as G13. {
    apply Succ.IsOrdinal. apply G1. assumption. }
  assert (:1: :< :N) as G14. { apply Omega.HasOne. }
  assert (Ordinal :1:) as G15. { apply Natural.OneIsOrdinal. }
  remember (shiftL b) as b' eqn:H12.
  remember (shiftL m) as m' eqn:H13.
  remember (fun i => a :^: b'!i :*: m'!i) as F' eqn:H14.
  assert (OrdFunOn b' n) as G16. { rewrite H12. apply SOL.OnSucc. assumption. }
  assert (OrdFunOn m' n) as G17. { rewrite H13. apply SOL.OnSucc. assumption. }
  assert (Decreasing b') as G18. {
    rewrite H12. apply SOL.IsDecreasing. 2: assumption. apply H3. }
  assert (:1: :< a) as G19. { apply Limit.HasOne. assumption. }
  assert (forall i, i :< n -> m'!i :< a) as G20. {
    intros i G20.
    assert (Ordinal i) as K1. { apply Core.IsOrdinal with n; assumption. }
    apply Omega.InLimitIncl. 1: assumption.
    rewrite H13, SOL.Eval.
    - apply H7. apply Succ.ElemCompat; assumption.
    - apply H4.
    - rewrite G8. apply Succ.ElemCompat; assumption. }
  assert (forall i, i :< n -> b'!i :< b!:0:) as G21. {
    intros i G21.
    assert (Ordinal i) as K1. { apply Core.IsOrdinal with n; assumption. }
    rewrite H12, SOL.Eval.
    - apply H5.
      + rewrite G7. apply Succ.HasZero. assumption.
      + rewrite G7. apply Succ.ElemCompat; assumption.
      + apply Succ.HasZero. assumption.
    - apply H3.
    - rewrite G7. apply Succ.ElemCompat; assumption. }
  remember (:sum:_{n} :[F']:) as s' eqn:H15.
  assert (forall i, i :< n -> Ordinal b'!i) as G22. {
    intros i G22. apply OrdFunOn.IsOrdinal with n; assumption. }
  assert (forall i, i :< n -> Ordinal m'!i) as G23. {
    intros i G23. apply OrdFunOn.IsOrdinal with n; assumption. }
  assert (forall i, i :< n -> Ordinal (:[F']:!i)) as G24. {
    intros i G24. rewrite ToFun.Eval, H14.
    apply Mult.IsOrdinal.
    - apply Exp.IsOrdinal. 1: assumption. apply G22. assumption.
    - apply G23. assumption. }
  assert (Ordinal s') as G25. {
    rewrite H15. apply SumOfClass.IsOrdinal; assumption. }
  assert (Ordinal (F :0:)) as G26. {
    rewrite H10. apply Mult.IsOrdinal.
    - apply Exp.IsOrdinal; assumption.
    - apply G2. assumption. }
  assert (Ordinal m!:0:) as G27. { apply G2. assumption. }
  assert (Ordinal (a :^: b!:0:)) as G28. { apply Exp.IsOrdinal; assumption. }
  assert (s = :[F]:!:0: :+: :sum:_{n} (COL.shiftL :[F]:)) as H16. {
    rewrite H11. apply SumOfClass.ShiftL; try assumption.
    - apply ToFun.IsFunctional.
    - intros i H16. apply ToFun.DomainOf. }
  rewrite ToFun.Eval in H16.
  assert (s' = :sum:_{n} (COL.shiftL :[F]:)) as H17. {
    rewrite H15. apply SumOfClass.EqualCharac. 1: assumption.
    intros i H17.
    assert (Ordinal i) as K1. { apply Core.IsOrdinal with n; assumption. }
    rewrite ToFun.Eval, COL.Eval, ToFun.Eval,
    H14, H10, H12, H13, SOL.Eval, SOL.Eval. 1: reflexivity.
    - apply H4.
    - rewrite G8. apply Succ.ElemCompat; assumption.
    - apply H3.
    - rewrite G7. apply Succ.ElemCompat; assumption.
    - apply ToFun.IsFunctional.
    - apply ToFun.DomainOf. }
  assert (s = F :0: :+: s') as H18. { rewrite H17. assumption. }
  assert (s' :< a :^: b!:0:) as H19. {
    rewrite H15, H14. apply IsElem; assumption. }
  rewrite H18, H10, <- Plus.WhenOneR, Mult.DistribL, Mult.WhenOneR;
  try assumption. apply Plus.ElemCompatR; try assumption.
  apply Mult.IsOrdinal; assumption.
Qed.

Proposition Exists : forall (a b:U),
  Ordinal a                                             ->
  Ordinal b                                             ->
  :1: :< a                                              ->
  exists n c d,
    n :< :N                                             /\
    OrdFunOn c n                                        /\
    OrdFunOn d n                                        /\
    Decreasing d                                        /\
    (forall i, i :< n -> :0: :< c!i)                    /\
    (forall i, i :< n -> c!i :< a  )                    /\
    b = :sum:_{n} :[fun i => a :^: d!i :*: c!i]:.
Proof.
  intros a b H1 H2 H3. revert b H2.
  remember (fun b =>
    :0: :< b                                                    ->
    exists n c d,
      n :< :N                                                   /\
      OrdFunOn c n                                              /\
      OrdFunOn d n                                              /\
      Decreasing d                                              /\
      (forall i, i :< n -> :0: :< c!i)                          /\
      (forall i, i :< n -> c!i :< a)                            /\
      b = :sum:_{n} :[fun i => a :^: d!i :*: c!i]:) as A eqn:E.
  assert (forall b, Ordinal b -> A b) as H4. {
    apply Induction.Induction. intros b H2 IH. rewrite E. intros H4.
    assert (exists e,
      Ordinal e /\ a :^: e :<=: b /\ b :< a :^: succ e) as H5. {
        apply Exp.InBetween; assumption. }
      destruct H5 as [e [H5 [H6 H7]]].
    assert (Ordinal (a :^: e)) as G1. { apply Exp.IsOrdinal; assumption. }
    assert (Ordinal :0:) as G2. { apply Core.ZeroIsOrdinal. }
    assert (Ordinal :1:) as G3. { apply Natural.OneIsOrdinal. }
    assert (:0: :< a) as G4. {
      apply ElemElemTran with :1:; try assumption.
      apply Succ.IsIn. }
    assert (exists q r,
      Ordinal q                 /\
      Ordinal r                 /\
      b = a :^: e :*: q :+: r   /\
      r :< a :^: e) as H8. {
        apply Mult.Euclid; try assumption.
        apply Exp.HasZero; assumption. }
    destruct H8 as [q [r [H8 [H9 [H10 H11]]]]].
    assert (Ordinal (a :^: e :*: q)) as G5. {
      apply Mult.IsOrdinal; assumption. }
    assert (:0: :< q) as H12. {
      assert (q = :0: \/ :0: :< q) as H12. { apply Core.ZeroOrElem. assumption. }
      destruct H12 as [H12|H12]. 2: assumption. subst. exfalso.
      rewrite Mult.WhenZeroR, Plus.WhenZeroL in H6. 2: assumption.
      assert (r :< r) as H13. { apply H6. assumption. }
      revert H13. apply NoElemLoop1. }
    assert (q :< a) as H13. {
      assert (q :< a \/ a :<=: q) as H13. { apply Core.ElemOrIncl; assumption. }
      destruct H13 as [H13|H13]. 1: assumption. exfalso.
      assert (a :^: succ e :<=: b) as H14. {
        rewrite Exp.WhenSuccR, H10. 2: assumption.
        apply Incl.Tran with (a :^: e :*: q).
      - apply Mult.InclCompatR; assumption.
      - apply Plus.IsInclR; assumption. }
      assert (b :< b) as H15. { apply H14. assumption. }
      revert H15. apply NoElemLoop1. }
    assert (r = :0: \/ :0: :< r) as H14. { apply Core.ZeroOrElem. assumption. }
    assert (:1: :< :N) as G6. { apply Omega.HasOne. }
    assert (:1: = succ :0:) as G7. { reflexivity. }
    assert (Ordinal :0:) as G8. { apply Core.ZeroIsOrdinal. }
    destruct H14 as [H14|H14].
    - remember :{ :(:0:,q): }: as c eqn:H15.
      remember :{ :(:0:,e): }: as d eqn:H16.
      assert (OrdFunOn c :1:) as H17. {
        rewrite H15. apply OrdFunOn.WhenSingle with q.
        1: assumption. reflexivity. }
      assert (OrdFunOn d :1:) as H18. {
        rewrite H16. apply OrdFunOn.WhenSingle with e.
        1: assumption. reflexivity. }
      assert (Decreasing d) as H19. {
        rewrite H16. apply Decreasing.WhenSingle with :0: e. reflexivity. }
      assert (forall i, i :< :1: -> :0: :< c!i) as H20. {
        intros i H20. rewrite Natural.OneExtension in H20.
        apply Single.Charac in H20. rewrite H20. clear H20.
        rewrite (Eval.WhenSingle :0: q c); assumption. }
      assert (forall i, i :< :1: -> c!i :< a) as H21. {
        intros i H21. rewrite Natural.OneExtension in H21.
        apply Single.Charac in H21. rewrite H21. clear H21.
        rewrite (Eval.WhenSingle :0: q c); assumption. }
      exists :1:, c, d. split. 1: assumption. split. 1: assumption.
      split. 1: assumption. split. 1: assumption. split. 1: assumption.
      split. 1: assumption.
      rewrite G7, SumOfClass.WhenSucc, SumOfClass.WhenZero, Plus.WhenZeroL;
      try assumption.
      rewrite ToFun.Eval, (Eval.WhenSingle :0: q c), (Eval.WhenSingle :0: e d);
      try assumption.
      + rewrite H14, Plus.WhenZeroR in H10. assumption.
      + rewrite ToFun.Eval, (Eval.WhenSingle :0: q c), (Eval.WhenSingle :0: e d);
        assumption.
    - assert (a :^: e :*: :1: :<=: a :^: e :*: q) as H15. {
        apply Mult.InclCompatR; try assumption.
        apply Succ.ElemIsIncl; assumption. }
      rewrite Mult.WhenOneR in H15. 2: assumption.
      assert (a :^: e :<=: b) as H16. {
        apply Incl.Tran with (a :^: e :*: q). 1: assumption.
        rewrite H10. apply Plus.IsInclR; assumption. }
      assert (r :< b) as H17. { apply H16. assumption. }
      assert (A r) as H18. { apply IH. assumption. }
      rewrite E in H18. specialize (H18 H14).
      destruct H18 as [n [c [d [H18 [H19 [H20 [H21 [H22 [H23 H24]]]]]]]]].
      assert (Ordinal n) as G23. { apply Omega.HasOrdinalElem. assumption. }
      remember (shiftR e d) as d' eqn:H25.
      remember (shiftR q c) as c' eqn:H26.
      exists (succ n), c', d'.
      assert (succ n :< :N) as G9. { apply Omega.HasSucc. assumption. }
      assert (OrdFunOn c' (succ n)) as H27. {
        rewrite H26. apply SOR.IsOrdFunOnNat; assumption. }
      assert (OrdFunOn d' (succ n)) as H28. {
        rewrite H25. apply SOR.IsOrdFunOnNat; assumption. }
      assert (forall i, i :< n -> d!i :< e) as H29. {
        intros i H29.
        assert (Ordinal d!i) as G10. {
          apply OrdFunOn.IsOrdinal with n; assumption. }
        assert (Ordinal (a :^: d!i)) as G11. { apply Exp.IsOrdinal; assumption. }
        apply Exp.ElemCompatRevR with a; try assumption.
        apply Core.InclElemTran with r; try assumption.
        apply Incl.Tran with (a :^: d!i :*: c!i).
        - apply Mult.IsInclR. 1: assumption.
          + apply OrdFunOn.IsOrdinal with n; assumption.
          + apply H22. assumption.
        - rewrite H24.
          assert (a :^: d!i :*: c!i
            = :[fun i => a :^: d!i :*: c!i]:!i) as H30. {
            symmetry. apply (ToFun.Eval (fun i => a :^: d!i :*: c!i)). }
          rewrite H30. apply SumOfClass.IsIncl; try assumption.
          + intros j H31. exists (a :^: d!j :*: c!j).
            apply ToFun.Charac2. reflexivity.
          + intros j H31. rewrite ToFun.Eval.
            apply Mult.IsOrdinal.
            * apply Exp.IsOrdinal. 1: assumption.
              apply OrdFunOn.IsOrdinal with n; assumption.
            * apply OrdFunOn.IsOrdinal with n; assumption. }
      assert (OrdFun c) as G10. { apply H19. }
      assert (OrdFun d) as G11. { apply H20. }
      assert (domain c = n) as G12. { apply H19. }
      assert (domain d = n) as G13. { apply H20. }
      assert (Functional c) as G14. { apply H19. }
      assert (Functional d) as G15. { apply H20. }
      assert (Ordinal :N) as G16. { apply Omega.IsOrdinal. }
      assert (domain c :<=: :N) as G17. {
        rewrite G12. apply Core.ElemIsIncl; assumption. }
      assert (domain d :<=: :N) as G18. {
        rewrite G13. apply Core.ElemIsIncl; assumption. }
      assert (Ordinal (succ n)) as G19. {
        apply Omega.HasOrdinalElem. assumption. }
      assert (Decreasing d') as H30. {
        rewrite H25. apply SOR.IsDecreasing; try assumption;
        rewrite G13;assumption. }
      assert (forall i, i :< succ n -> :0: :< c'!i) as H31. {
        intros i H31.
        assert (i :< :N) as G20. {
          apply Omega.IsIn with (succ n); assumption. }
        assert (Ordinal i) as G21. { apply Omega.HasOrdinalElem. assumption. }
        assert (i = :0: \/ :0: :< i) as H32. {
          apply Core.ZeroOrElem. assumption. }
        destruct H32 as [H32|H32].
        - rewrite H26, H32, SOR.EvalZero; assumption.
        - apply Omega.HasPred in H32. 2: assumption.
          destruct H32 as [j [H32 H33]].
          assert (Ordinal j) as G22. { apply Omega.HasOrdinalElem. assumption. }
          assert (j :< n) as G24. {
            apply Succ.ElemCompatRev; try assumption.
            rewrite <- H33. assumption. }
          rewrite H26, H33, SOR.EvalSucc; try assumption.
          + apply H22. assumption.
          + rewrite G12. assumption. }
      assert (forall i, i :< succ n -> c'!i :< a) as H32. {
        intros i H32.
        assert (i :< :N) as G20. {
          apply Omega.IsIn with (succ n); assumption. }
        assert (Ordinal i) as G21. { apply Omega.HasOrdinalElem. assumption. }
        assert (i = :0: \/ :0: :< i) as H33. {
          apply Core.ZeroOrElem. assumption. }
        destruct H33 as [H33|H33].
        - rewrite H26, H33, SOR.EvalZero; assumption.
        - apply Omega.HasPred in H33. 2: assumption.
          destruct H33 as [j [H33 H34]].
          assert (Ordinal j) as G22. { apply Omega.HasOrdinalElem. assumption. }
          assert (j :< n) as G24. {
            apply Succ.ElemCompatRev; try assumption.
            rewrite <- H34. assumption. }
          rewrite H26, H34, SOR.EvalSucc; try assumption.
          + apply H23. assumption.
          + rewrite G12. assumption. }
      split. 1: assumption. split. 1: assumption. split. 1: assumption.
      split. 1: assumption. split. 1: assumption. split. 1: assumption.
      remember (fun i => a :^: d!i :*: c!i) as F eqn:H33.
      remember (fun i => a :^: d'!i :*: c'!i) as G eqn:H34.
      remember (COR.shiftR (a :^: e :*: q) :[F]:) as H eqn:H35.
      assert (:sum:_{succ n} (:[G]:) = :sum:_{succ n} H) as H36. {
        apply SumOfClass.EqualCharac. 1: assumption. intros i H36.
        rewrite H34, H35, ToFun.Eval, H25, H26.
        assert (i :< :N) as G20. {
          apply Omega.IsIn with (succ n); assumption. }
        assert (Ordinal i) as G21. { apply Omega.HasOrdinalElem. assumption. }
        assert (i = :0: \/ :0: :< i) as H37. {
          apply Core.ZeroOrElem. assumption. }
        destruct H37 as [H37|H37].
        - rewrite H37, SOR.EvalZero, SOR.EvalZero, COR.EvalZero; try assumption.
          1: reflexivity. apply ToFun.IsFunctional.
        - apply Omega.HasPred in H37. 2: assumption.
          destruct H37 as [j [H37 H38]].
          assert (Ordinal j) as G22. { apply Omega.HasOrdinalElem. assumption. }
          assert (j :< n) as G24. {
            apply Succ.ElemCompatRev; try assumption.
            rewrite <- H38. assumption. }
          assert (j :< domain c) as G25. { rewrite G12. assumption. }
          assert (j :< domain d) as G26. { rewrite G13. assumption. }
          rewrite H38, SOR.EvalSucc, SOR.EvalSucc, COR.EvalSucc, H33, ToFun.Eval;
          try assumption. 1: reflexivity.
          + apply ToFun.IsFunctional.
          + apply ToFun.DomainOf. }
      rewrite H36, H35.
      assert (:sum:_{succ n} (COS.shiftR (a :^: e :*: q) :[F]:)
        = a :^: e :*: q :+: :sum:_{n} :[F]:) as H37. {
          apply SumOfClass.ShiftR; try assumption.
          - apply ToFun.IsFunctional.
          - intros j H37. apply ToFun.DomainOf.
          - intros j H37. rewrite ToFun.Eval, H33.
            apply Mult.IsOrdinal.
            + apply Exp.IsOrdinal. 1: assumption.
              apply OrdFunOn.IsOrdinal with n; assumption.
            + apply OrdFunOn.IsOrdinal with n; assumption. }
      assert (b = :sum:_{succ n} (COS.shiftR (a :^: e :*: q) :[F]:)) as X. 2: apply X.
      rewrite H37, H10, H24. reflexivity. }
  intros b H2.
  assert (b = :0: \/ :0: :< b) as H5. { apply Core.ZeroOrElem. assumption. }
  destruct H5 as [H5|H5].
  - exists :0:, :0:, :0:.
    assert (:0: :< :N) as H6. { apply Omega.HasZero. }
    assert (OrdFunOn :0: :0:) as H7. { apply OrdFunOn.WhenEmpty. reflexivity. }
    assert (Decreasing :0:) as H8. { apply Decreasing.WhenEmpty. reflexivity. }
    assert (forall i, i :< :0: -> :0: :< :0:!i) as H9. {
      intros i H9. apply Empty.Charac in H9. contradiction. }
    assert (forall i, i :< :0: -> :0:!i :< a) as H10. {
      intros i H10. apply Empty.Charac in H10. contradiction. }
    split. 1: assumption. split. 1: assumption. split. 1: assumption.
    split. 1: assumption. split. 1: assumption. split. 1: assumption.
    rewrite H5, SumOfClass.WhenZero. reflexivity.
  - rewrite E in H4. apply H4; assumption.
Qed.

Proposition IsElemEuclid : forall (a b c q1 q2 r1 r2:U),
  Ordinal a                                           ->
  Ordinal b                                           ->
  Ordinal c                                           ->
  Ordinal q1                                          ->
  Ordinal q2                                          ->
  Ordinal r1                                          ->
  Ordinal r2                                          ->
  :1: :< a                                            ->
  q1  :< a                                            ->
  r1  :< a :^: b                                      ->
  :0: :< q2                                           ->
  b   :< c                                            ->
  a :^: b :*: q1 :+: r1 :< a :^: c :*: q2 :+: r2.
Proof.
  intros a b c q1 q2 r1 r2 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12.
  assert (Ordinal (succ b)) as G1. { apply Succ.IsOrdinal. assumption. }
  assert (:0: :< a) as G2. { apply Natural.HasZero; assumption. }
  assert (Ordinal (a :^: c)) as G3. { apply Exp.IsOrdinal; assumption. }
  assert (Ordinal (a :^: c :*: q2)) as G4. { apply Mult.IsOrdinal; assumption. }
  assert (Ordinal (a :^: b)) as G5. { apply Exp.IsOrdinal; assumption. }
  assert (Ordinal (a :^: b :*: q1)) as G6. { apply Mult.IsOrdinal; assumption. }
  assert (succ q1 :<=: a) as G7. { apply Succ.ElemIsIncl; assumption. }
  assert (succ b :<=: c) as G8. { apply Succ.ElemIsIncl; assumption. }
  assert (Ordinal :1:) as G9. { apply Natural.OneIsOrdinal. }
  assert (Ordinal (a :^: b :*: q1 :+: r1)) as G10. {
    apply Plus.IsOrdinal; assumption. }
  assert (Ordinal (succ q1)) as G11. { apply Succ.IsOrdinal. assumption. }
  assert (Ordinal (a :^: b :*: (succ q1))) as G12. {
    apply Mult.IsOrdinal; assumption. }
  assert (Ordinal (a :^: b :*: a)) as G13. {
    apply Mult.IsOrdinal; assumption. }
  assert (Ordinal (a :^: (succ b))) as G14. { apply Exp.IsOrdinal; assumption. }
  assert (Ordinal (a :^: c :*: q2 :+: r2)) as G15. {
    apply Plus.IsOrdinal; assumption. }
  assert (a :^: succ b :<=: a :^: c) as H13. { apply Exp.InclCompatR; assumption. }
  assert (a :^: succ b :<=: a :^: c :*: q2) as H14. {
    apply Incl.Tran with (a :^: c). 1: assumption.
    apply Mult.IsInclR; assumption. }
  assert (a :^: succ b :<=: a :^: c :*: q2 :+: r2) as H15. {
    apply Incl.Tran with (a :^: c :*: q2). 1: assumption.
    apply Plus.IsInclR; assumption. }
  assert (a :^: b :*: q1 :+: r1 :< a :^: b :*: q1 :+: a :^: b) as H16. {
    apply Plus.ElemCompatR; assumption. }
  assert (a :^: b :*: q1 :+: r1 :< a :^: b :*: (succ q1)) as H17. {
    rewrite <- Plus.WhenOneR, Mult.DistribL, Mult.WhenOneR; assumption. }
  assert (a :^: b :*: q1 :+: r1 :< a :^: (succ b)) as H18. {
    rewrite <- Plus.WhenOneR, Exp.DistribL, Exp.WhenOneR; try assumption.
    apply Core.ElemInclTran with (a :^: b :*: (succ q1)); try assumption.
    apply Mult.InclCompatR; assumption. }
  apply Core.ElemInclTran with (a :^: (succ b)); assumption.
Qed.

Proposition IsUnique : forall (a n m c d e f:U),
  Ordinal a                                       ->
  :1: :< a                                        ->
  n :< :N                                         ->
  m :< :N                                         ->
  OrdFunOn c n                                    ->
  OrdFunOn d n                                    ->
  OrdFunOn e m                                    ->
  OrdFunOn f m                                    ->
  Decreasing d                                    ->
  Decreasing f                                    ->
  (forall i, i :< n -> :0: :< c!i)                ->
  (forall i, i :< n -> c!i :< a  )                ->
  (forall i, i :< m -> :0: :< e!i)                ->
  (forall i, i :< m -> e!i :< a  )                ->
  :sum:_{n} (:[fun i => a :^: d!i :*: c!i]:)       =
  :sum:_{m} (:[fun i => a :^: f!i :*: e!i]:)      ->
  n = m /\ c = e /\ d = f.
Proof.
  intros a n m c d e f H1 H2 H3. revert n H3 m c d e f.
  assert (Ordinal :0:) as K1. { apply Core.ZeroIsOrdinal. }
  assert (Ordinal :1:) as K2. { apply Natural.OneIsOrdinal. }
  assert (:0: :< a) as K3. { apply Natural.HasZero; assumption. }
  remember (fun n =>
    forall m c d e f : U,
    m :< :N                                                             ->
    OrdFunOn c n                                                        ->
    OrdFunOn d n                                                        ->
    OrdFunOn e m                                                        ->
    OrdFunOn f m                                                        ->
    Decreasing d                                                        ->
    Decreasing f                                                        ->
    (forall i, i :< n -> :0: :< c!i)                                    ->
    (forall i, i :< n -> c!i :< a  )                                    ->
    (forall i, i :< m -> :0: :< e!i)                                    ->
    (forall i, i :< m -> e!i  :< a )                                    ->
    :sum:_{ n} (:[ fun i : U => a :^: (d) ! (i) :*: (c) ! (i) ]:) =
      :sum:_{ m} (:[ fun i : U => a :^: (f) ! (i) :*: (e) ! (i) ]:)     ->
    n = m /\ c = e /\ d = f) as A eqn:E.
  assert (forall n, n :< :N -> A n) as H3. {
    apply Omega.Induction; rewrite E.
    - intros m c d e f H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14.
      remember (fun i => a :^: d!i :*: c!i) as F1 eqn:E1.
      remember (fun i => a :^: f!i :*: e!i) as F2 eqn:E2.
      assert (Ordinal m) as G1. { apply Omega.HasOrdinalElem. assumption. }
      rewrite SumOfClass.WhenZero in H14.
      assert (:0: = m) as H15. {
        assert (m = :0: \/ :0: :< m) as H15. {
          apply Core.ZeroOrElem. assumption. }
        destruct H15 as [H15|H15]. 1: { symmetry. assumption. } exfalso.
        apply Omega.HasPred in H15. 2: assumption.
        destruct H15 as [k [H15 H16]].
        assert (Ordinal k) as G2. { apply Omega.HasOrdinalElem. assumption. }
        rewrite H16, SumOfClass.WhenSucc, ToFun.Eval in H14. 2: assumption.
        assert (k :< m) as G3. { rewrite H16. apply Succ.IsIn. }
        assert (Ordinal (e!k)) as G4. {
          apply OrdFunOn.IsOrdinal with m; assumption. }
        assert (Ordinal (f!k)) as G5. {
          apply OrdFunOn.IsOrdinal with m; assumption. }
        assert (forall i, i :< m -> Ordinal (F2 i)) as G6. {
          intros i G6. rewrite E2. apply Mult.IsOrdinal.
          - apply Exp.IsOrdinal. 1: assumption.
            apply OrdFunOn.IsOrdinal with m; assumption.
          - apply OrdFunOn.IsOrdinal with m; assumption. }
        assert (Ordinal (F2 k)) as G7. { apply G6. assumption. }
        assert (Ordinal (:sum:_{k} :[F2]:)) as G8. {
          apply SumOfClass.IsOrdinal. 1: assumption.
          intros i G8. rewrite ToFun.Eval. apply G6.
          apply Core.ElemElemTran with k; try assumption.
            apply Omega.HasOrdinalElem, Omega.IsIn with k; assumption. }
        assert (F2 k :<=: (:sum:_{k} :[F2]:) :+: F2 k) as H17. {
          apply Plus.IsInclL; assumption. }
        rewrite <- H14 in H17.
        assert (:0: :< F2 k) as H18. {
          rewrite E2. apply Mult.HasZero. 2: assumption.
          - apply Exp.IsOrdinal; assumption.
          - apply Exp.HasZero; assumption.
          - apply H12. assumption. }
        assert (:0: :< :0:) as H19. { apply H17. assumption. }
        apply Empty.Charac in H19. contradiction. }
        rewrite <- H15 in H6. rewrite <- H15 in H7.
        assert (c = :0:) as H20. { apply OrdFunOn.WhenEmpty. assumption. }
        assert (d = :0:) as H21. { apply OrdFunOn.WhenEmpty. assumption. }
        assert (e = :0:) as H22. { apply OrdFunOn.WhenEmpty. assumption. }
        assert (f = :0:) as H23. { apply OrdFunOn.WhenEmpty. assumption. }
        assert (c = e) as H24. { subst. reflexivity. }
        assert (d = f) as H25. { subst. reflexivity. }
        split. 1: assumption. split; assumption.
    - intros n H3 IH m c d e f H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15.
      remember (fun i => a :^: d!i :*: c!i) as F1 eqn:E1.
      remember (fun i => a :^: f!i :*: e!i) as F2 eqn:E2.
      assert (Ordinal n) as G1. { apply Omega.HasOrdinalElem. assumption. }
      assert (Ordinal m) as G2. { apply Omega.HasOrdinalElem. assumption. }
      assert (succ n :< :N) as G3. { apply Omega.HasSucc. assumption. }
      assert (Ordinal (succ n)) as G4. {
        apply Omega.HasOrdinalElem. assumption. }
      assert (m =:0: \/ :0: :< m) as H16. { apply Core.ZeroOrElem. assumption. }
      destruct H16 as [H16|H16].
      + exfalso.
        rewrite H16, SumOfClass.WhenZero, SumOfClass.WhenSucc, ToFun.Eval in H15.
        2: assumption.
        assert (n :< succ n) as G5. { apply Succ.IsIn. }
        assert (Ordinal (c!n)) as G6. {
          apply OrdFunOn.IsOrdinal with (succ n); assumption. }
        assert (Ordinal (d!n)) as G7. {
          apply OrdFunOn.IsOrdinal with (succ n); assumption. }
        assert (forall i, i :< succ n -> Ordinal (F1 i)) as G8. {
          intros i G8. rewrite E1. apply Mult.IsOrdinal.
          - apply Exp.IsOrdinal. 1: assumption.
            apply OrdFunOn.IsOrdinal with (succ n); assumption.
          - apply OrdFunOn.IsOrdinal with (succ n); assumption. }
        assert (Ordinal (F1 n)) as G9. { apply G8. assumption. }
        assert (Ordinal (:sum:_{n} :[F1]:)) as G10. {
          apply SumOfClass.IsOrdinal. 1: assumption.
          intros i G10. rewrite ToFun.Eval. apply G8.
          apply Core.ElemElemTran with n; try assumption.
            apply Omega.HasOrdinalElem, Omega.IsIn with n; assumption. }
        assert (F1 n :<=: (:sum:_{n} :[F1]:) :+: F1 n) as H17. {
          apply Plus.IsInclL; assumption. }
        rewrite H15 in H17.
        assert (:0: :< F1 n) as H18. {
          rewrite E1. apply Mult.HasZero. 2: assumption.
          - apply Exp.IsOrdinal; assumption.
          - apply Exp.HasZero; assumption.
          - apply H11. assumption. }
        assert (:0: :< :0:) as H19. { apply H17. assumption. }
        apply Empty.Charac in H19. contradiction.
      + apply Omega.HasPred in H16. 2: assumption. destruct H16 as [k [H16 H17]].
        assert (forall i, i :< m -> Ordinal (F2 i)) as G5. {
          intros i G5. rewrite E2. apply Mult.IsOrdinal.
          - apply Exp.IsOrdinal. 1: assumption.
            apply OrdFunOn.IsOrdinal with m; assumption.
          - apply OrdFunOn.IsOrdinal with m; assumption. }
        assert (forall i, i :< succ n -> Ordinal (F1 i)) as G6. {
          intros i G6. rewrite E1. apply Mult.IsOrdinal.
          - apply Exp.IsOrdinal. 1: assumption.
            apply OrdFunOn.IsOrdinal with (succ n); assumption.
          - apply OrdFunOn.IsOrdinal with (succ n); assumption. }
        assert (Functional c) as G7. { apply H5. }
        assert (Functional d) as G8. { apply H6. }
        assert (Functional e) as G9. { apply H7. }
        assert (Functional f) as G10. { apply H8. }
        assert (domain c = succ n) as G11. { apply H5. }
        assert (domain d = succ n) as G12. { apply H6. }
        assert (domain e = m) as G13. { apply H7. }
        assert (domain f = m) as G14. { apply H8. }
        assert (Ordinal k) as G15. { apply Omega.HasOrdinalElem. assumption. }
        assert (F1 :0: :+: (:sum:_{n} (COL.shiftL :[F1]:))
          = F2 :0: :+: (:sum:_{k} (COL.shiftL :[F2]:))) as H18. {
            rewrite H17, SumOfClass.ShiftL, SumOfClass.ShiftL,
            ToFun.Eval, ToFun.Eval in H15; try assumption.
            - apply ToFun.IsFunctional.
            - intros i H18. apply ToFun.DomainOf.
            - intros i H18. rewrite ToFun.Eval. apply G5.
              rewrite H17. assumption.
            - apply ToFun.IsFunctional.
            - intros i H18. apply ToFun.DomainOf.
            - intros i H18. rewrite ToFun.Eval. apply G6. assumption. }
        clear H15.
        remember (SOL.shiftL c) as c' eqn:H19.
        remember (SOL.shiftL d) as d' eqn:H20.
        remember (SOL.shiftL e) as e' eqn:H21.
        remember (SOL.shiftL f) as f' eqn:H22.
        remember (fun i => a :^: d'!i :*: c'!i) as F1' eqn:E1'.
        remember (fun i => a :^: f'!i :*: e'!i) as F2' eqn:E2'.
        assert (:sum:_{n} (COS.shiftL :[F1]:) = :sum:_{n} :[F1']:) as H23. {
          apply SumOfClass.EqualCharac. 1: assumption. intros i H23.
          assert (Ordinal i) as G16. { apply Core.IsOrdinal with n; assumption. }
          rewrite COL.Eval, ToFun.Eval, ToFun.Eval, E1, E1', H19, H20,
            SOL.Eval, SOL.Eval; try assumption. 1: reflexivity.
          - rewrite G11. apply Succ.ElemCompat; assumption.
          - rewrite G12. apply Succ.ElemCompat; assumption.
          - apply ToFun.IsFunctional.
          - apply ToFun.DomainOf. }
        assert (:sum:_{k} (COS.shiftL :[F2]:) = :sum:_{k} :[F2']:) as H24. {
          apply SumOfClass.EqualCharac. 1: assumption. intros i H24.
          assert (Ordinal i) as G16. { apply Core.IsOrdinal with k; assumption. }
          rewrite COL.Eval, ToFun.Eval, ToFun.Eval, E2, E2', H21, H22,
            SOL.Eval, SOL.Eval; try assumption. 1: reflexivity.
          - rewrite G13, H17. apply Succ.ElemCompat; assumption.
          - rewrite G14, H17. apply Succ.ElemCompat; assumption.
          - apply ToFun.IsFunctional.
          - apply ToFun.DomainOf. }
        rewrite H23, H24 in H18. clear H23 H24.
        assert (Ordinal d!:0:) as G16. {
          apply OrdFunOn.IsOrdinal with (succ n). 1: assumption.
          apply Succ.HasZero. assumption. }
        assert (Ordinal f!:0:) as G17. {
          apply OrdFunOn.IsOrdinal with m. 1: assumption.
          rewrite H17. apply Succ.HasZero. assumption. }
        assert (OrdFunOn c' n) as G18. {
          rewrite H19. apply SOL.OnSucc. assumption. }
        assert (OrdFunOn d' n) as G19. {
          rewrite H20. apply SOL.OnSucc. assumption. }
        assert (OrdFunOn e' k) as G20. {
          rewrite H21. apply SOL.OnSucc. rewrite <- H17. assumption. }
        assert (OrdFunOn f' k) as G21. {
          rewrite H22. apply SOL.OnSucc. rewrite <- H17. assumption. }
        assert (Decreasing d') as G22. {
          rewrite H20. apply SOL.IsDecreasing. 2: assumption. apply H6. }
        assert (Decreasing f') as G23. {
          rewrite H22. apply SOL.IsDecreasing. 2: assumption. apply H8. }
        assert (forall i, i :< n -> c'!i :< a) as G24. {
          rewrite H19. intros i G24.
          assert (Ordinal i) as G25. { apply Core.IsOrdinal with n; assumption. }
          rewrite SOL.Eval. 2: assumption.
          - apply H12. apply Succ.ElemCompat; assumption.
          - rewrite G11. apply Succ.ElemCompat; assumption. }
        assert (forall i, i :< k -> e'!i :< a) as G25. {
          rewrite H21. intros i G25.
          assert (Ordinal i) as G26. { apply Core.IsOrdinal with k; assumption. }
          rewrite SOL.Eval. 2: assumption.
          - apply H14. rewrite H17. apply Succ.ElemCompat; assumption.
          - rewrite G13, H17. apply Succ.ElemCompat; assumption. }
        assert (forall i, i :< n -> d'!i :< d!:0:) as G26. {
          rewrite H20. intros i G26.
          assert (Ordinal i) as G27. { apply Core.IsOrdinal with n; assumption. }
          rewrite SOL.Eval. 2: assumption.
          - apply H9.
            + rewrite G12. apply Succ.HasZero. assumption.
            + rewrite G12. apply Succ.ElemCompat; assumption.
            + apply Succ.HasZero. assumption.
          - rewrite G12. apply Succ.ElemCompat; assumption. }
        assert (forall i, i :< k -> f'!i :< f!:0:) as G27. {
          rewrite H22. intros i G27.
          assert (Ordinal i) as G28. { apply Core.IsOrdinal with k; assumption. }
          rewrite SOL.Eval. 2: assumption.
          - apply H10.
            + rewrite G14, H17. apply Succ.HasZero. assumption.
            + rewrite G14, H17. apply Succ.ElemCompat; assumption.
            + apply Succ.HasZero. assumption.
          - rewrite G14, H17. apply Succ.ElemCompat; assumption. }
        assert ((:sum:_{n} :[F1']:) :< a :^: d!:0:) as H23. {
          rewrite E1'. apply IsElem; assumption. }
        assert ((:sum:_{k} :[F2']:) :< a :^: f!:0:) as H24. {
          rewrite E2'. apply IsElem; assumption. }
        assert (forall i, i :< succ n -> Ordinal c!i) as G29. {
          intros i G29. apply OrdFunOn.IsOrdinal with (succ n); assumption. }
        assert (forall i, i :< m -> Ordinal e!i) as G30. {
          intros i G30. apply OrdFunOn.IsOrdinal with m; assumption. }
        assert (forall i, i :< succ n -> Ordinal d!i) as G31. {
          intros i G31. apply OrdFunOn.IsOrdinal with (succ n); assumption. }
        assert (forall i, i :< m -> Ordinal f!i) as G32. {
          intros i G32. apply OrdFunOn.IsOrdinal with m; assumption. }
        assert (forall i, i :< n -> Ordinal c'!i) as G33. {
          rewrite H19. intros i G33.
          assert (Ordinal i) as G34. { apply Core.IsOrdinal with n; assumption. }
          rewrite SOL.Eval. 2: assumption.
          - apply G29. apply Succ.ElemCompat; assumption.
          - rewrite G11. apply Succ.ElemCompat; assumption. }
        assert (forall i, i :< n -> Ordinal d'!i) as G34. {
          rewrite H20. intros i G34.
          assert (Ordinal i) as G35. { apply Core.IsOrdinal with n; assumption. }
          rewrite SOL.Eval. 2: assumption.
          - apply G31. apply Succ.ElemCompat; assumption.
          - rewrite G12. apply Succ.ElemCompat; assumption. }
        assert (forall i, i :< k -> Ordinal e'!i) as G35. {
          rewrite H21. intros i G35.
          assert (Ordinal i) as G36. { apply Core.IsOrdinal with k; assumption. }
          rewrite SOL.Eval. 2: assumption.
          - apply G30. rewrite H17. apply Succ.ElemCompat; assumption.
          - rewrite G13, H17. apply Succ.ElemCompat; assumption. }
        assert (forall i, i :< k -> Ordinal f'!i) as G36. {
          rewrite H22. intros i G36.
          assert (Ordinal i) as G37. { apply Core.IsOrdinal with k; assumption. }
          rewrite SOL.Eval. 2: assumption.
          - apply G32. rewrite H17. apply Succ.ElemCompat; assumption.
          - rewrite G14, H17. apply Succ.ElemCompat; assumption. }
        assert (Ordinal (:sum:_{n} :[F1']:)) as G37. {
          apply SumOfClass.IsOrdinal. 1: assumption.
          intros i G37. rewrite ToFun.Eval, E1'.
          apply Mult.IsOrdinal.
          - apply Exp.IsOrdinal. 1: assumption. apply G34. assumption.
          - apply G33. assumption. }
        assert (Ordinal (:sum:_{k} :[F2']:)) as G38. {
          apply SumOfClass.IsOrdinal. 1: assumption.
          intros i G38. rewrite ToFun.Eval, E2'.
          apply Mult.IsOrdinal.
          - apply Exp.IsOrdinal. 1: assumption. apply G36. assumption.
          - apply G35. assumption. }
        assert (Ordinal c!:0:) as G39. {
          apply OrdFunOn.IsOrdinal with (succ n). 1: assumption.
          apply Succ.HasZero. assumption. }
        assert (Ordinal e!:0:) as G40. {
          apply OrdFunOn.IsOrdinal with m. 1: assumption.
          rewrite H17. apply Succ.HasZero. assumption. }
        remember (:sum:_{n} :[F1']:) as r1 eqn:H25.
        remember (:sum:_{k} :[F2']:) as r2 eqn:H26.
        rewrite E1, E2 in H18.
        remember (a :^: d!:0: :*: c!:0: :+: r1) as s1 eqn:H27.
        remember (a :^: f!:0: :*: e!:0: :+: r2) as s2 eqn:H28.
        assert (d!:0: = f!:0:) as H29. {
          assert (d!:0: = f!:0: \/ d!:0: :< f!:0: \/ f!:0: :< d!:0:) as H29. {
            apply Core.IsTotal; assumption. }
          destruct H29 as [H29|[H29|H29]]. 1: assumption.
          - exfalso.
            assert (s1 :< s2) as H30. {
            rewrite H27, H28. apply IsElemEuclid; try assumption.
            + apply H12, Succ.HasZero. assumption.
            + apply H13. rewrite H17. apply Succ.HasZero. assumption. }
            assert (s2 :< s2) as H31. { rewrite H18 in H30. assumption. }
            revert H31. apply NoElemLoop1.
          - exfalso.
            assert (s2 :< s1) as H30. {
            rewrite H27, H28. apply IsElemEuclid; try assumption.
            + apply H14. rewrite H17. apply Succ.HasZero. assumption.
            + apply H11, Succ.HasZero. assumption. }
            assert (s2 :< s2) as H31. { rewrite H18 in H30. assumption. }
            revert H31. apply NoElemLoop1. }
        assert (c!:0: = e!:0: /\ r1 = r2) as H30. {
          apply Mult.EuclidUnique with (a :^: f!:0:); try assumption.
          - apply Exp.IsOrdinal; assumption.
          - rewrite <- H29. assumption.
          - rewrite H27, H28, H29 in H18. assumption. }
        destruct H30 as [H30 H31].
        assert (forall i, i :< n -> :0: :< c'!i) as G41. {
          rewrite H19. intros i G41.
          assert (Ordinal i) as G42. { apply Core.IsOrdinal with n; assumption. }
          rewrite SOL.Eval. 2: assumption.
          - apply H11. apply Succ.ElemCompat; assumption.
          - rewrite G11. apply Succ.ElemCompat; assumption. }
        assert (forall i, i :< k -> :0: :< e'!i) as G42. {
          rewrite H21. intros i G42.
          assert (Ordinal i) as G43. { apply Core.IsOrdinal with k; assumption. }
          rewrite SOL.Eval. 2: assumption.
          - apply H13. rewrite H17. apply Succ.ElemCompat; assumption.
          - rewrite G13, H17. apply Succ.ElemCompat; assumption. }
        assert (n = k /\ c' = e' /\ d' = f') as H32. {
          apply IH; try assumption.
          rewrite H25, H26, E1', E2' in H31. assumption. }
        destruct H32 as [H32 [H33 H34]].
        assert (succ n = m) as H35. { rewrite H32. symmetry. assumption. }
        assert (c = e) as H36. {
          apply SOL.IsEqual with n; try assumption.
          - rewrite <- H35 in H7. assumption.
          - rewrite H19, H21 in H33. assumption. }
        assert (d = f) as H37. {
          apply SOL.IsEqual with n; try assumption.
          - rewrite <- H35 in H8. assumption.
          - rewrite H20, H22 in H34. assumption. }
        split. 1: assumption. split; assumption. }
  rewrite E in H3. assumption.
Qed.

Proposition MultReduceNIncl : forall (a b c d n:U),
  Ordinal a                                                       ->
  Ordinal d                                                       ->
  n :< :N                                                         ->
  OrdFunOn b (succ n)                                             ->
  OrdFunOn c (succ n)                                             ->
  :1: :< a                                                        ->
  Decreasing b                                                    ->
  (forall i, i :< succ n -> :0: :< c!i)                           ->
  (forall i, i :< succ n -> c!i :< a )                            ->
  :N :<=: d                                                       ->
  (:sum:_{succ n} :[fun i => a :^: b!i :*: c!i]:) :*: a :^: d      =
  a :^: (b!:0: :+: d).
Proof.
  intros a b c d n H1 H2 H3 H4 H5 Ha H6 H7 H8 H9.
  remember (fun i => a :^: b!i :*: c!i) as F eqn:H10.
  remember (:sum:_{succ n} :[F]:) as s eqn:H11.
  assert (forall i, i :< succ n -> Ordinal b!i) as G1. {
    intros i G1. apply OrdFunOn.IsOrdinal with (succ n); assumption. }
  assert (forall i, i :< succ n -> Ordinal c!i) as G2. {
    intros i G2. apply OrdFunOn.IsOrdinal with (succ n); assumption. }
  assert (Ordinal n) as G3. { apply Omega.HasOrdinalElem. assumption. }
  assert (succ n :< :N) as G4. { apply Omega.HasSucc. assumption. }
  assert (:0: :< succ n) as G5. { apply Omega.SuccHasZero. assumption. }
  assert (forall i, i :< succ n -> Ordinal (:[F]:!i)) as G6. {
    intros i G6. rewrite ToFun.Eval, H10.
    apply Mult.IsOrdinal.
    - apply Exp.IsOrdinal. 1: assumption. apply G1. assumption.
    - apply G2. assumption. }
  assert (domain b = succ n) as G7. { apply H4. }
  assert (domain c = succ n) as G8. { apply H5. }
  assert (Ordinal (a :^: d)) as G9. { apply Exp.IsOrdinal; assumption. }
  assert (Ordinal (succ n)) as G10. { apply Succ.IsOrdinal. assumption. }
  assert (Ordinal s) as G11. {
    rewrite H11. apply SumOfClass.IsOrdinal. 1: assumption.
    intros i G11. apply G6. assumption. }
  assert (Ordinal b!:0:) as G12. { apply G1. assumption. }
  assert (Ordinal (succ b!:0:)) as G13. {
    apply Succ.IsOrdinal. apply G1. assumption. }
  assert (:1: :< :N) as G14. { apply Omega.HasOne. }
  assert (Ordinal :1:) as G15. { apply Natural.OneIsOrdinal. }
  assert (a :^: b!:0: :<=: a :^: b!:0: :*: c!:0:) as H12. {
    apply Mult.IsInclR.
    - apply Exp.IsOrdinal. 1: assumption. apply G1. assumption.
    - apply G2. assumption.
    - apply H7. assumption. }
  assert (a :^: b!:0: :<=: s) as H13. {
    apply Incl.Tran with (a :^: b!:0: :*: c!:0:). 1: assumption.
    assert (:[F]:!:0: :<=: :sum:_{succ n} :[F]:) as H13. {
      apply SumOfClass.IsIncl; try assumption.
      intros i H13. apply ToFun.DomainOf. }
    rewrite ToFun.Eval, H10 in H13. rewrite H11, H10. assumption. }
  assert (s :< a :^: succ b!:0:) as H14. {
    rewrite H11, H10. apply IsElem; try assumption.
    intros i H14.
    assert (i :< :N) as K1. { apply Omega.IsIn with (succ n); assumption. }
    assert (i = :0: \/ :0: :< i) as H15. { apply Omega.ZeroOrElem. assumption. }
    destruct H15 as [H15|H15].
    - subst. apply Succ.IsIn.
    - apply ElemElemTran with b!:0:.
      + apply G1. assumption.
      + apply G1. assumption.
      + apply Succ.IsOrdinal, G1. assumption.
      + apply H6; try assumption; rewrite G7; assumption.
      + apply Succ.IsIn. }
  assert (s :*: a :^: d :<=: a :^: (succ b!:0: :+: d)) as H15. {
    rewrite Exp.DistribL; try assumption.
    apply Mult.InclCompatL; try assumption.
    - apply Exp.IsOrdinal; assumption.
    - apply Core.ElemIsIncl. 2: assumption. apply Exp.IsOrdinal; assumption. }
  assert (s :*: a :^: d :<=: a :^: (b!:0: :+: d)) as H16. {
    rewrite <- Plus.WhenOneR, Plus.Assoc, (Plus.WhenNatL :1: d) in H15;
    assumption. }
  assert (a :^: (b!:0: :+: d) :<=: s :*: a :^: d) as H17. {
    rewrite Exp.DistribL; try assumption.
    apply Mult.InclCompatL; try assumption.
    apply Exp.IsOrdinal; assumption. }
  apply Incl.DoubleInclusion. split; assumption.
Qed.

Proposition MultReduceNatLimitL: forall (a b d m n:U),
  Limit a                                                         ->
  Ordinal d                                                       ->
  n :< :N                                                         ->
  OrdFunOn b (succ n)                                             ->
  OrdFunOn m (succ n)                                             ->
  Decreasing b                                                    ->
  :0: :< m!:0:                                                    ->
  (forall i, i :< succ n -> m!i :< :N)                            ->
  :0: :< d                                                        ->
  (:sum:_{succ n} :[fun i => a :^: b!i :*: m!i]:) :*: a :^: d      =
  a :^: (b!:0: :+: d).
Proof.
  intros a b d m n H1 H2 H3 H4 H5 H6 H7 H8 H9.
  remember (fun i => a :^: b!i :*: m!i) as F eqn:H10.
  remember (:sum:_{succ n} :[F]:) as s eqn:H11.
  assert (Ordinal a) as G0. { apply H1. }
  assert (forall i, i :< succ n -> Ordinal b!i) as G1. {
    intros i G1. apply OrdFunOn.IsOrdinal with (succ n); assumption. }
  assert (forall i, i :< succ n -> Ordinal m!i) as G2. {
    intros i G2. apply OrdFunOn.IsOrdinal with (succ n); assumption. }
  assert (Ordinal n) as G3. { apply Omega.HasOrdinalElem. assumption. }
  assert (succ n :< :N) as G4. { apply Omega.HasSucc. assumption. }
  assert (:0: :< succ n) as G5. { apply Omega.SuccHasZero. assumption. }
  assert (forall i, i :< succ n -> Ordinal (:[F]:!i)) as G6. {
    intros i G6. rewrite ToFun.Eval, H10.
    apply Mult.IsOrdinal.
    - apply Exp.IsOrdinal. 1: assumption. apply G1. assumption.
    - apply G2. assumption. }
  assert (domain b = succ n) as G7. { apply H4. }
  assert (domain m = succ n) as G8. { apply H5. }
  assert (Ordinal (a :^: d)) as G9. { apply Exp.IsOrdinal; assumption. }
  assert (Ordinal (succ n)) as G10. { apply Succ.IsOrdinal. assumption. }
  assert (Ordinal s) as G11. {
    rewrite H11. apply SumOfClass.IsOrdinal. 1: assumption.
    intros i G11. apply G6. assumption. }
  assert (Ordinal b!:0:) as G12. { apply G1. assumption. }
  assert (Ordinal (succ b!:0:)) as G13. {
    apply Succ.IsOrdinal. apply G1. assumption. }
  assert (:1: :< :N) as G14. { apply Omega.HasOne. }
  assert (Ordinal :1:) as G15. { apply Natural.OneIsOrdinal. }
  assert (:1: :< a) as G19. { apply Limit.HasOne. assumption. }
  assert (Ordinal (F :0:)) as G26. {
    rewrite H10. apply Mult.IsOrdinal.
    - apply Exp.IsOrdinal; assumption.
    - apply G2. assumption. }
  assert (Ordinal m!:0:) as G27. { apply G2. assumption. }
  assert (Ordinal (a :^: b!:0:)) as G28. { apply Exp.IsOrdinal; assumption. }
  assert (a :^: b!:0: :<=: a :^: b!:0: :*: m!:0:) as H20. {
    apply Mult.IsInclR. 3: assumption.
    - apply Exp.IsOrdinal; assumption.
    - apply G2. assumption. }
  assert (a :^: b!:0: :<=: s) as H21. {
    apply Incl.Tran with  (F :0:).
    - rewrite H10. assumption.
    - assert (:[F]:!:0: :<=: s) as H21. {
        rewrite H11. apply SumOfClass.IsIncl; try assumption.
        intros i H21. apply ToFun.DomainOf. }
      rewrite ToFun.Eval in H21. assumption. }
  assert (s :< a :^: b!:0: :*: succ m!:0:) as H23. {
    rewrite H11, H10. apply IsElemNat; assumption. }
  assert (a :^: (b!:0: :+: d) :<=: s :*: a :^: d) as H24. {
    rewrite Exp.DistribL; try assumption.
    apply Mult.InclCompatL; assumption. }
  assert (s :*: a :^: d :<=: a :^: b!:0: :*: succ m!:0: :*: a :^: d) as H25. {
    apply Mult.InclCompatL; try assumption.
    - apply Mult.IsOrdinal. 1: assumption. apply Succ.IsOrdinal. assumption.
    - apply Core.ElemIsIncl. 2: assumption.
      apply Mult.IsOrdinal. 1: assumption. apply Succ.IsOrdinal. assumption. }
  assert (s :*: a :^: d :<=: a :^: b!:0: :*: a :^: d) as H26. {
    rewrite Mult.Assoc, (Mult.LimitWithNatSimple (succ m!:0:)) in H25;
    try assumption.
    - apply Omega.HasSucc, H8, Succ.HasZero. assumption.
    - apply Exp.IsLimitL; assumption.
    - apply Succ.HasZero. assumption.
    - apply Succ.IsOrdinal. assumption. }
  assert (s :*: a :^: d :<=: a :^: (b!:0: :+: d)) as H27. {
    rewrite Exp.DistribL; assumption. }
  apply Incl.DoubleInclusion. split; assumption.
Qed.

Lemma LimitWithNat : forall (a b c n:U),
  Limit a                                                         ->
  Ordinal b                                                       ->
  Ordinal c                                                       ->
  n :< :N                                                         ->
  :0: :< b                                                        ->
  :0: :< n                                                        ->
  :0: :< c                                                        ->
  Successor c /\ (a :^: b :*: n) :^: c = a :^: (b :*: c) :*: n    \/
  Limit c     /\ (a :^: b :*: n) :^: c = a :^: (b :*: c).
Proof.
  intros a b c n H1 H2 H3 H4 H5 H6. revert c H3.
  assert (Ordinal a) as G1. { apply H1. }
  assert (Ordinal n) as G2. { apply Omega.HasOrdinalElem. assumption. }
  assert (Ordinal (a :^: b)) as G3. { apply Exp.IsOrdinal; assumption. }
  assert (Ordinal (a :^: b :*: n)) as G4. { apply Mult.IsOrdinal; assumption. }
  assert (Limit (a :^: b)) as G5. { apply IsLimitL; assumption. }
  assert (n :*: a :^: b = a :^: b) as G6. {
    apply Mult.LimitWithNatSimple; assumption. }
  assert (:0: :< a) as G7. { apply Limit.HasZero. assumption. }
  assert (:0: :< a :^: b) as G8. { apply Exp.HasZero; assumption. }
  assert (:0: :< a :^: b :*: n) as G9. { apply Mult.HasZero; assumption. }
  assert (Ordinal :0:) as G10. { apply Core.ZeroIsOrdinal. }
  assert (n :< a :^: b) as G11. { apply Omega.InLimitIncl; assumption. }
  assert (Ordinal :1:) as G12. { apply Natural.OneIsOrdinal. }
  remember (fun c => :0: :< c ->
    Successor c /\ (a :^: b :*: n) :^: c = a :^: (b :*: c) :*: n \/
    Limit c     /\ (a :^: b :*: n) :^: c = a :^: (b :*: c)) as A eqn:E.
  assert (forall c, Ordinal c -> A c) as H7. {
    apply Induction2.Induction; rewrite E.
    - intros H7. apply Empty.Charac in H7. contradiction.
    - intros c H3 IH _. left. split. 1: { apply Succ.IsSuccessor. assumption. }
      assert (Ordinal (b :*: c)) as K1. { apply Mult.IsOrdinal; assumption. }
      assert (Ordinal (a :^: (b :*: c))) as K2. {
        apply Exp.IsOrdinal; assumption. }
      assert (c = :0: \/ :0: :< c) as H7. { apply Core.ZeroOrElem. assumption. }
      destruct H7 as [H7|H7].
      + subst. rewrite Exp.WhenOneR, Mult.WhenOneR; try assumption. reflexivity.
      + specialize (IH H7). destruct IH as [[H8 IH]|[H8 IH]].
        * rewrite Exp.WhenSuccR, IH, Mult.Assoc, <- (Mult.Assoc n (a :^: b)), G6,
          <- Mult.Assoc, <- Exp.DistribL, <- Mult.WhenSuccR; try assumption.
          reflexivity.
        * rewrite Exp.WhenSuccR, IH, <- Mult.Assoc, <- Exp.DistribL,
          <- Mult.WhenSuccR; try assumption. reflexivity.
    - intros c H3 IH _. right. split. 1: assumption.
      assert (Ordinal c) as K1. { apply H3. }
      assert (Ordinal (b :*: c)) as K2. { apply Mult.IsOrdinal; assumption. }
      assert (Ordinal (a :^: (b :*: c))) as K3. { apply Exp.IsOrdinal; assumption. }
      assert (a :^: (b :*: c) :<=: (a :^: b :*: n) :^: c) as H7. {
        rewrite <- Exp.Assoc; try assumption.
        apply Exp.InclCompatL; try assumption.
        apply Mult.IsInclR; assumption. }
      assert ((a :^: b :*: n) :^: c :<=: a :^: (b :*: c)) as H8. {
        intros x H8.
        rewrite Exp.WhenLimit in H8; try assumption.
        apply SUG.Charac in H8. destruct H8 as [d [H8 H9]].
        assert (Ordinal d) as L1. { apply Core.IsOrdinal with c; assumption. }
        assert (Ordinal (b :*: d)) as L2. { apply Mult.IsOrdinal; assumption. }
        assert (Ordinal (a :^: (b :*: d))) as L3. {
          apply Exp.IsOrdinal; assumption. }
        assert (Ordinal (succ d)) as L4. { apply Succ.IsOrdinal. assumption. }
        assert (x :< (a :^: b :*: n) :^: d) as H10. { assumption. } clear H9.
        assert ((a :^: b :*: n) :^: d :<=: (a :^: (b :*: d) :*: n)) as H11. {
          assert (d = :0: \/ :0: :< d) as H11. {
            apply Core.ZeroOrElem. assumption. }
          destruct H11 as [H11|H11].
          - subst. rewrite Exp.WhenZeroR, Mult.WhenZeroR, Exp.WhenZeroR,
            Mult.WhenOneL. 2: assumption. apply Succ.ElemIsIncl; assumption.
          - specialize (IH d H8 H11).
            destruct IH as [[H9 IH]|[H9 IH]]; rewrite IH.
            + apply Incl.Refl.
            + apply Mult.IsInclR; assumption. }
        assert (a :^: (b :*: d) :*: n :<=: a :^: (b :*: succ d)) as H12. {
          rewrite <- Plus.WhenOneR, Mult.DistribL, Mult.WhenOneR, Exp.DistribL;
          try assumption. apply Mult.InclCompatR; try assumption.
          apply Core.ElemIsIncl; assumption. }
        apply H11, H12 in H10.
        rewrite <- Exp.Assoc, Exp.WhenLimit; try assumption.
        apply SUG.Charac. exists (succ d). split.
        - apply Limit.HasSucc; assumption.
        - assert (x :< (a :^: b) :^: (succ d)) as X. 2: apply X. (* rewrite *)
          rewrite Exp.Assoc; assumption. }
      apply Incl.DoubleInclusion. split; assumption. }
  rewrite E in H7. assumption.
Qed.

Proposition LimitWithNatSucc : forall (a b c n:U),
  Limit a                                                         ->
  Ordinal b                                                       ->
  Successor c                                                     ->
  n :< :N                                                         ->
  :0: :< b                                                        ->
  :0: :< n                                                        ->
  (a :^: b :*: n) :^: c = a :^: (b :*: c) :*: n.
Proof.
  intros a b c n H1 H2 H3 H4 H5 H6.
  assert (Ordinal c) as G1. { apply H3. }
  assert (
    Successor c /\ (a :^: b :*: n) :^: c = a :^: (b :*: c) :*: n \/
    Limit c     /\ (a :^: b :*: n) :^: c = a :^: (b :*: c)) as H7. {
      apply LimitWithNat; try assumption.
      apply Succ.HasZero'. assumption. }
  destruct H7 as [[H7 H8]|[H7 H8]]. 1: assumption. exfalso.
  revert H3. apply Limit.NotSucc. assumption.
Qed.

Proposition LimitWithNatLimit : forall (a b c n:U),
  Limit a                                                         ->
  Ordinal b                                                       ->
  Limit c                                                         ->
  n :< :N                                                         ->
  :0: :< b                                                        ->
  :0: :< n                                                        ->
  (a :^: b :*: n) :^: c = a :^: (b :*: c).
Proof.
  intros a b c n H1 H2 H3 H4 H5 H6.
  assert (Ordinal c) as G1. { apply H3. }
  assert (
    Successor c /\ (a :^: b :*: n) :^: c = a :^: (b :*: c) :*: n \/
    Limit c     /\ (a :^: b :*: n) :^: c = a :^: (b :*: c)) as H7. {
      apply LimitWithNat; try assumption.
      apply Limit.HasZero. assumption. }
  destruct H7 as [[H7 H8]|[H7 H8]]. 2: assumption. exfalso.
  revert H7. apply Limit.NotSucc. assumption.
Qed.

Proposition LimitWithNatIncl : forall (a b c n:U),
  Limit a                                                         ->
  Ordinal b                                                       ->
  Ordinal c                                                       ->
  n :< :N                                                         ->
  :0: :< b                                                        ->
  :0: :< n                                                        ->
  (a :^: b :*: n) :^: c :<=: a :^: (b :*: c) :*: n.
Proof.
  intros a b c n H1 H2 H3 H4 H5 H6.
  assert (Ordinal n) as G1. { apply Omega.HasOrdinalElem. assumption. }
  assert (Ordinal :0:) as G2. { apply Core.ZeroIsOrdinal. }
  assert (Ordinal a) as G3. { apply H1. }
  assert (Ordinal (b :*: c)) as G4. { apply Mult.IsOrdinal; assumption. }
  assert (Ordinal (a :^: (b :*: c))) as G5. { apply Exp.IsOrdinal; assumption. }
  assert (c = :0: \/ :0: :< c) as H7. { apply Core.ZeroOrElem. assumption. }
  destruct H7 as [H7|H7].
  - subst.
    rewrite Exp.WhenZeroR, Mult.WhenZeroR, Exp.WhenZeroR, Mult.WhenOneL.
    2: assumption. apply Succ.ElemIsIncl; assumption.
  - assert (
      Successor c /\ (a :^: b :*: n) :^: c = a :^: (b :*: c) :*: n \/
      Limit c     /\ (a :^: b :*: n) :^: c = a :^: (b :*: c)) as H8. {
        apply LimitWithNat; assumption. }
    destruct H8 as [[H8 H9]|[H8 H9]]; rewrite H9.
    + apply Incl.Refl.
    + apply Mult.IsInclR; assumption.
Qed.

Proposition ExpNatIncl : forall (a b d m n:U),
  Limit a                                                         ->
  Ordinal d                                                       ->
  n :< :N                                                         ->
  OrdFunOn b (succ n)                                             ->
  OrdFunOn m (succ n)                                             ->
  Decreasing b                                                    ->
  :0: :< b!:0:                                                    ->
  (forall i, i :< succ n -> m!i :< :N)                            ->
  (:sum:_{succ n} :[fun i => a :^: b!i :*: m!i]:) :^: d         :<=:
  a :^: (b!:0: :*: d) :*: (succ m!:0:).
Proof.
  intros a b d m n H1 H2 H3 H4 H5 H6 H7 H8.
  assert (Ordinal a) as G1. { apply H1. }
  assert (forall i, i :< succ n -> Ordinal b!i) as G2. {
    intros i G2. apply OrdFunOn.IsOrdinal with (succ n); assumption. }
  assert (forall i, i :< succ n -> Ordinal m!i) as G3. {
    intros i G3. apply OrdFunOn.IsOrdinal with (succ n); assumption. }
  assert (Ordinal n) as G4. { apply Omega.HasOrdinalElem. assumption. }
  assert (Ordinal b!:0:) as G5. { apply G2. apply Succ.HasZero. assumption. }
  assert (Ordinal m!:0:) as G6. { apply G3. apply Succ.HasZero. assumption. }
  assert (Ordinal (succ m!:0:)) as G7. { apply Succ.IsOrdinal. assumption. }
  assert (Ordinal (a :^: b!:0:)) as G8. { apply Exp.IsOrdinal; assumption. }
  assert (Ordinal (a :^: b!:0: :*: succ m!:0:)) as G9. {
    apply Mult.IsOrdinal; assumption. }
  remember (:sum:_{succ n} :[fun i => a :^: b!i :*: m!i]:) as s eqn:H9.
  assert (Ordinal (succ n)) as G10. { apply Succ.IsOrdinal. assumption. }
  assert (Ordinal s) as G11. {
    rewrite H9. apply SumOfClass.IsOrdinal; try assumption.
    intros i G11. rewrite ToFun.Eval.
    apply Mult.IsOrdinal.
    - apply Exp.IsOrdinal. 1: assumption. apply G2. assumption.
    - apply G3. assumption. }
  assert (succ m!:0: :< :N) as G12. {
    apply Omega.HasSucc, H8, Succ.HasZero. assumption. }

  assert (s :<=: a :^: b!:0: :*: succ m!:0:) as H10. {
    apply Core.ElemIsIncl. 1: assumption.
    rewrite H9. apply IsElemNat; assumption. }
  assert (s :^: d :<=: (a :^: b!:0: :*: succ m!:0:) :^: d) as H11. {
    apply Exp.InclCompatL; assumption. }
  assert (
    (a :^: b!:0: :*: succ m!:0:) :^: d
    :<=:
    a :^: (b!:0: :*: d) :*: succ m!:0:) as H12. {
      apply LimitWithNatIncl; try assumption.
      apply Succ.HasZero. assumption. }
  apply Incl.Tran with ((a :^: b!:0: :*: succ m!:0:) :^: d); assumption.
Qed.

Proposition ExpNatEqual : forall (a b d m n:U),
  Limit a                                                         ->
  Limit d                                                         ->
  n :< :N                                                         ->
  OrdFunOn b (succ n)                                             ->
  OrdFunOn m (succ n)                                             ->
  Decreasing b                                                    ->
  :0: :< b!:0:                                                    ->
  :0: :< m!:0:                                                    ->
  (forall i, i :< succ n -> m!i :< :N)                            ->
  (:sum:_{succ n} :[fun i => a :^: b!i :*: m!i]:) :^: d            =
  a :^: (b!:0: :*: d).
Proof.
  intros a b d m n H1 H2 H3 H4 H5 H6 H7 H8 H9.
  remember (:sum:_{succ n} :[fun i => a :^: b!i :*: m!i]:) as s eqn:H10.
  assert (Ordinal a) as G1. { apply H1. }
  assert (forall i, i :< succ n -> Ordinal b!i) as G2. {
    intros i G2. apply OrdFunOn.IsOrdinal with (succ n); assumption. }
  assert (forall i, i :< succ n -> Ordinal m!i) as G3. {
    intros i G3. apply OrdFunOn.IsOrdinal with (succ n); assumption. }
  assert (Ordinal n) as G4. { apply Omega.HasOrdinalElem. assumption. }
  assert (Ordinal b!:0:) as G5. { apply G2. apply Succ.HasZero. assumption. }
  assert (Ordinal m!:0:) as G6. { apply G3. apply Succ.HasZero. assumption. }
  assert (Ordinal (succ m!:0:)) as G7. { apply Succ.IsOrdinal. assumption. }
  assert (Ordinal (a :^: b!:0:)) as G8. { apply Exp.IsOrdinal; assumption. }
  assert (Ordinal (a :^: b!:0: :*: succ m!:0:)) as G9. {
    apply Mult.IsOrdinal; assumption. }
  assert (Ordinal (succ n)) as G10. { apply Succ.IsOrdinal. assumption. }
  assert (Ordinal s) as G11. {
    rewrite H10. apply SumOfClass.IsOrdinal; try assumption.
    intros i G11. rewrite ToFun.Eval.
    apply Mult.IsOrdinal.
    - apply Exp.IsOrdinal. 1: assumption. apply G2. assumption.
    - apply G3. assumption. }
  assert (succ m!:0: :< :N) as G12. {
    apply Omega.HasSucc, H9, Succ.HasZero. assumption. }
  assert (Ordinal d) as G14. { apply H2. }
  assert (s :<=: a :^: b!:0: :*: succ m!:0:) as H11. {
    apply Core.ElemIsIncl. 1: assumption.
    rewrite H10. apply IsElemNat; assumption. }
  assert (a :^: b!:0: :<=: a :^: b!:0: :*: m!:0:) as H12. {
    apply Mult.IsInclR; assumption. }
  remember (fun i => a :^: b!i :*: m!i) as F eqn:G13.
  assert (a :^: b!:0: :*: m!:0: :<=: s) as H13. {
    assert (:[F]:!:0: :<=: :sum:_{succ n} :[F]:) as H13. {
      apply SumOfClass.IsIncl.
      - apply Omega.HasSucc. assumption.
      - apply Succ.HasZero. assumption.
      - intros i H13. apply ToFun.DomainOf.
      - intros i H13. rewrite ToFun.Eval, G13.
        apply Mult.IsOrdinal.
        + apply Exp.IsOrdinal. 1: assumption. apply G2. assumption.
        +apply G3. assumption. }
    rewrite ToFun.Eval, G13 in H13.
    rewrite H10, G13. assumption. }
  assert (a :^: b!:0: :<=: s) as H14. {
    apply Incl.Tran with (a :^: b!:0: :*: m!:0:); assumption. }
  assert (a :^: (b!:0: :*: d) :<=: s :^: d) as H15. {
    rewrite <- Exp.Assoc; try assumption.
    apply Exp.InclCompatL; assumption. }
  assert (s :^: d :<=: (a :^: b!:0: :*: succ m!:0:) :^: d) as H16. {
    apply Exp.InclCompatL; assumption. }
  assert ((a :^: b!:0: :*: succ m!:0:) :^: d = a :^: (b!:0: :*: d)) as H17. {
    apply LimitWithNatLimit; try assumption.
    apply Succ.HasZero. assumption. }
  rewrite H17 in H16. apply Incl.DoubleInclusion. split; assumption.
Qed.

Proposition ExpExpNatEqual : forall (a b d m n:U),
  Limit a                                                         ->
  Ordinal d                                                       ->
  n :< :N                                                         ->
  OrdFunOn b (succ n)                                             ->
  OrdFunOn m (succ n)                                             ->
  Decreasing b                                                    ->
  :0: :< b!:0:                                                    ->
  :0: :< m!:0:                                                    ->
  :0: :< d                                                        ->
  (forall i, i :< succ n -> m!i :< :N)                            ->
  (:sum:_{succ n} :[fun i => a :^: b!i :*: m!i]:) :^: (a :^: d)    =
  a :^: (b!:0: :*: a :^: d).
Proof.
  intros a b d m n H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.
  apply ExpNatEqual; try assumption.
  apply IsLimitL; assumption.
Qed.
