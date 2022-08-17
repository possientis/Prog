{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeInType             #-}
{-# LANGUAGE TypeOperators          #-}

module Stitch.CSE 
  ( cse 
  ) where

{- GENERAL APPROACH

We do CSE in three steps:

1. Recur through an expression. At every point in the AST with more than
   one subexpression (e.g., App, Cond, etc.), check to see if the same
   subsubexpression appears in more than subexpression. For example,
   App (... blah ...) (... blah ...). If so, add a new let-binding for
   the common subsubexpression. This is done by insertLets.

2. Recur through an expression. For every Let, remember the let-bound
   variable's RHS in a map. If that expression is seen, replace the expression
   with the let-bound variable. This is done by replaceExprs.

3. Recur through an expression. For every Let, do two things:
   a. If the RHS of the let-bound variable is just a variable, map the LHS to
      the RHS, applying the mapping to the body of the let.
   b. If the let-bound variable is not used in its body, remove the Let entirely.
   This is done in zapLets.

   This last step is important because step 1 inserts a new Let for every common
   subsubexpression, even if there is a larger subsubexpression to be commoned
   up. Zapping the lets removes the cruft that step 1 might insert. Step 1 also
   will insert a Let at every interior node where multiple subexpressions have
   a subsubexpression in common; if a subsubexpression appears in *three* places,
   then we'll get two Lets, one at the top join and one at the lower join. (Indeed,
   this duplication of Lets is why we need part (a) of step 3.)
-}

import Data.Kind
import Data.Type.Equality
import Type.Reflection    (typeRep)

import Stitch.Data.Exists
import Stitch.Data.IHashable
import Stitch.Data.Nat
import Stitch.Data.Vec
import Stitch.Exp
import Stitch.Shift
import Stitch.Type
import Stitch.Utils


import qualified Stitch.Data.IHashMap.Lazy    as M
import qualified Stitch.Data.IHashSet         as S

---------------------------------------------------------------------
-- The main types for the data structures used in this file

-- | A mapping from expressions in a certain context to a type indexed
-- by the type of expression it is stored with
type ExpMap ctx a = M.IHashMap (Exp ctx) a

-- | A set of expressions in a certain context
type ExpSet ctx   = S.IHashSet (Exp ctx)

-- | Perform common-subexpression elimination (CSE)
cse 
  :: forall (n :: Nat) (ctx :: Ctx n) (ty :: Type)
   . KnownLength ctx 
  => Exp ctx ty 
  -> Exp ctx ty
cse = zapLets . replaceExprs . fst . insertLet

---------------------------------------------------------------------
-- Step 1. insertLets

-- | Implements Step 1 from the general description of CSE, above
insertLet 
  :: forall (n :: Nat) (ctx :: Ctx n) (ty :: Type)
   .  KnownLength ctx 
  =>  Exp ctx ty 
  -> (Exp ctx ty, ExpSet ctx)
insertLet = \case
  e@(Var {})        -> (e, S.empty)

  (Lam arg_ty e1)   -> mk_result e' [unshiftSet all_exprs]
    where
      (e1', all_exprs) = insertLet e1
      e' = Lam arg_ty e1' 
    
  (App e1 e2)       -> mk_result e' [all_exprs1, all_exprs2]
    where
      (e1', all_exprs1) = insertLet e1
      (e2', all_exprs2) = insertLet e2
      e' = App e1' e2'
    
  (Let e1 e2)       -> mk_result e' [all_exprs1, unshiftSet all_exprs2] 
    where
      (e1', all_exprs1) = insertLet e1
      (e2', all_exprs2) = insertLet e2
      e' = Let e1' e2'

  (Arith e1 op e2)  -> mk_result e' [all_exprs1, all_exprs2]
    where
      (e1', all_exprs1) = insertLet e1
      (e2', all_exprs2) = insertLet e2
      e' = Arith e1' op e2'
    
  (Cond e1 e2 e3)   -> mk_result e' [all_exprs1, all_exprs2, all_exprs3]
    where 
      (e1', all_exprs1) = insertLet e1
      (e2', all_exprs2) = insertLet e2
      (e3', all_exprs3) = insertLet e3
      e' = Cond e1' e2' e3'
    
  (Fix e1)          -> mk_result e' [all_exprs]
    where
      (e1', all_exprs) = insertLet e1
      e' = Fix e1'
    
  e@(IntE {})       -> (e, S.empty)

  e@(BoolE {})      -> (e, S.empty)

mk_result
  :: forall (n :: Nat) (ctx :: Ctx n) (ty :: Type)
   . KnownLength ctx 
  => Exp ctx ty 
  -> [ExpSet ctx] 
  -> (Exp ctx ty, ExpSet ctx)
mk_result e alls = (mkLets common_exprs e, S.insert e all_exprs)
  where
    pairs        = allPairs alls
    inters       = map (uncurry S.intersection) pairs
    common_exprs = S.toList (S.unions inters)
    all_exprs    = S.unions alls


-- | A 'ShiftedExp' represents an expression that's been shifted into a deeper
-- context. Note the non-prenex kind, necessary so that Lets can be parameterized
-- by a partial application of this type.
newtype ShiftedExp ctx :: forall (n :: Nat) . Ctx n -> Type -> Type 
  where
    ShiftedExp :: Exp (prefix :++: ctx) ty -> ShiftedExp ctx prefix ty

-- | A snoc-list (the "nil" is at the left) of expressions, where later elements
-- are in a deeper context than earlier ones.
data Lets :: forall n. (forall m. Ctx m -> Type -> Type) -> Ctx n -> Type 
  where
    LNil  :: forall (a :: forall m. Ctx m -> Type -> Type). Lets a 'VNil
    (:<:) :: forall (a :: forall m. Ctx m -> Type -> Type) ctx ty
           . Lets a ctx -> a ctx ty -> Lets a (ty ':> ctx)

infixl 5 :<:

-- | Convert a list of expressions (of a variety of types) into a 'Lets' 
-- construct, in CPS-style.
expsToLets 
  :: [Ex (Exp ctx)]
  -> ( forall n (prefix :: Ctx n) 
     . Lets (ShiftedExp ctx) prefix 
    -> Length prefix 
    -> r
    )
  -> r
expsToLets []             k = k LNil LZ
expsToLets (Ex e : rest)  k = expsToLets rest $ \lets len ->
  k (lets :<: ShiftedExp (shifts len e)) (LS len)

-- | Wrap an expression in nested Lets. This version is efficient, 
-- shifting expressions by many levels at once.
mkLets 
  :: forall (n :: Nat) (ctx :: Ctx n) (ty :: Type)
   . [Ex (Exp ctx)] 
  -> Exp ctx ty 
  -> Exp ctx ty
mkLets exps body = expsToLets exps $ \ lets len -> mkLets_ lets (shifts len body)

mkLets_ 
  :: forall (m :: Nat) (n :: Nat) (ctx :: Ctx m) (prefix :: Ctx n) (ty :: Type)
   . Lets (ShiftedExp ctx) prefix 
  -> Exp (prefix :++: ctx) ty 
  -> Exp ctx ty
mkLets_ LNil                    body = body
mkLets_ (rest :<: ShiftedExp e) body = mkLets_ rest (Let e body)

-- | Wrap an expression in nested Lets. This version is very inefficient, doing
-- lots of single shifts.
_mkLetsSimple 
  :: forall (n :: Nat) (ctx :: Ctx n) (ty :: Type)
   . [Ex (Exp ctx)] 
  -> Exp ctx ty 
  -> Exp ctx ty
_mkLetsSimple []            body = body
_mkLetsSimple (Ex e : rest) body = Let e (shift (_mkLetsSimple rest body))

---------------------------------------------------------------------
-- Step 2. replaceExprs

-- | Implements Step 2 from the general description of CSE, above
replaceExprs :: KnownLength ctx => Exp ctx ty -> Exp ctx ty
replaceExprs = replace_ M.empty

replace_ 
  :: forall (n :: Nat) (ctx :: Ctx n) (ty :: Type)
   . KnownLength ctx 
  => ExpMap ctx (Elem ctx) 
  -> Exp ctx ty 
  -> Exp ctx ty

replace_ m e | Just v <- M.lookup e m = Var v

replace_ m (Let e1 e2) =  Let e1' (replace_ m' e2)
  where
    e1' = replace_ m e1
    m'  = add_mapping (shift e1) $ add_mapping (shift e1') (shiftMap m) 
    add_mapping e = insertIfAbsent e EZ

replace_ _ e@(Var {}) = e
replace_ m (Lam arg_ty e) = Lam arg_ty (replace_ (shiftMap m) e)
replace_ m (App e1 e2) = App (replace_ m e1) (replace_ m e2)
replace_ m (Arith e1 op e2) = Arith (replace_ m e1) op (replace_ m e2)
replace_ m (Cond e1 e2 e3) = Cond (replace_ m e1) (replace_ m e2) (replace_ m e3)
replace_ m (Fix e) = Fix (replace_ m e)
replace_ _ e@(IntE {}) = e
replace_ _ e@(BoolE {}) = e

insertIfAbsent 
  :: (TestEquality k, IHashable k)
  => k i 
  -> v i 
  -> M.IHashMap k v 
  -> M.IHashMap k v
insertIfAbsent k v m = M.alter (\case 
  Just v0 -> Just v0
  Nothing -> Just v) k m

---------------------------------------------------------------------
-- Step 3. zapLets

-- | Implements Step 3 from the general description of CSE, above
zapLets 
  :: forall (n :: Nat) (ctx :: Ctx n) (ty :: Type)
   . KnownLength ctx 
  => Exp ctx ty 
  -> Exp ctx ty
zapLets = fst . zapLets_ M.empty

zapLets_ 
  :: forall (n :: Nat) (ctx :: Ctx n) (ty :: Type)
   .  KnownLength ctx
  =>  M.IHashMap (Elem ctx) (Elem ctx)
  ->  Exp ctx ty
  -> (Exp ctx ty, S.IHashSet (Elem ctx))

zapLets_ m  = \case

  (Let e1 e2) 
    | Var v <- e1 -> 
      let (e2', used_vars) = zapLets_ (M.insert EZ (shift v) (shiftMap m)) e2
          e2''             = uncheckedUnshift e2' 
      in (e2'', unshiftSet used_vars)

    | otherwise  -> 
      let (e1', used_vars1) = zapLets_ m e1
          (e2', used_vars2) = zapLets_ (shiftMap m) e2
          used_vars2' = unshiftSet used_vars2 
      in if S.member EZ used_vars2
        then (Let e1' e2', S.unions [used_vars1, used_vars2'])
        else (uncheckedUnshift e2', used_vars2')

  e@(Var v) 
    | Just v' <- M.lookup v m -> (Var v', S.singleton v')
    | otherwise               -> (e, S.singleton v)

  (Lam arg_ty e) -> 
    let (e', used_vars) = zapLets_ (shiftMap m) e 
    in (Lam arg_ty e', unshiftSet used_vars)

  (App e1 e2) ->
    let (e1', used_vars1) = zapLets_ m e1
        (e2', used_vars2) = zapLets_ m e2 
    in (App e1' e2', used_vars1 `S.union` used_vars2)

  (Arith e1 op e2) ->
    let (e1', used_vars1) = zapLets_ m e1
        (e2', used_vars2) = zapLets_ m e2 
    in (Arith e1' op e2', used_vars1 `S.union` used_vars2)

  (Cond e1 e2 e3) ->
    let (e1', used_vars1) = zapLets_ m e1
        (e2', used_vars2) = zapLets_ m e2
        (e3', used_vars3) = zapLets_ m e3 
    in (Cond e1' e2' e3', S.unions [used_vars1, used_vars2, used_vars3])

  (Fix e) -> 
    let (e', used_vars) = zapLets_ m e 
    in (Fix e', used_vars)

  e@(IntE {})  -> (e, S.empty)

  e@(BoolE {}) -> (e, S.empty)

---------------------------------------------------------
-- Shifting utilities

shiftMap 
  :: forall 
      (a :: ShiftableKind)
      (b :: ShiftableKind)
      (n :: Nat) (ctx :: Ctx n) (ty :: Type)
   . ( IHashable (a (ty ':> ctx))
     , TestEquality (a (ty ':> ctx))
     , Shiftable a
     , Shiftable b 
     )
  => M.IHashMap (a ctx) (b ctx) 
  -> M.IHashMap (a (ty ':> ctx)) (b (ty ':> ctx))
shiftMap = M.foldrWithKey go M.empty
  where go e el m = M.insert (shift e) (shift el) m

unshiftSet 
  :: forall (a :: ShiftableKind) (n :: Nat) (ctx :: Ctx n) (ty :: Type)
   . (Shiftable a, TestEquality (a ctx), IHashable (a ctx))
  => S.IHashSet (a (ty ':> ctx))
  -> S.IHashSet (a ctx)
unshiftSet = S.foldr go S.empty
  where
    go e set
      | Just e' <- unshift e
      = S.insert e' set
      | otherwise
      = set

---------------------------------------------------------
-- Examples for testing

_testExp :: Exp 'VNil ((Int -> Int) -> Int -> Int)
_testExp = Lam (typeRep @Int :-> typeRep @Int) $
           Lam (typeRep @Int) $
           App (Lam (typeRep @Int) $
                App (Var (ES (ES EZ)))
                    (Var (ES EZ)))
               (App (Var (ES EZ))
                    (Var EZ))

_biggerExp :: Exp 'VNil ((Int -> Int) -> Int -> Int)
_biggerExp = Lam (typeRep @Int :-> typeRep @Int) $
             Lam (typeRep @Int) $
             App (Lam (typeRep @Int) $
                  App (Lam (typeRep @Int) $
                       App (Var (ES (ES (ES EZ))))
                           (Var (ES (ES EZ))))
                       (App (Var (ES (ES EZ)))
                            (Var (ES EZ))))
                 (App (Var (ES EZ))
                      (Var EZ))
