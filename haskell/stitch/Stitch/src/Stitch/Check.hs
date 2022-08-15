{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE PatternSynonyms  #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeInType       #-}

module Stitch.Check
  ( check
  ) where

import Control.Monad.Reader
import Control.Monad.Except
import Data.Kind
import Text.PrettyPrint.ANSI.Leijen
import Type.Reflection  hiding ( pattern App )

import Stitch.Data.Exists
import Stitch.Data.Fin
import Stitch.Data.Nat
import Stitch.Data.Singletons
import Stitch.Data.Vec
import Stitch.Exp
import Stitch.Globals
import Stitch.Op
import Stitch.Shift
import Stitch.Type
import Stitch.Unchecked
import Stitch.Utils


-- | Abort with a type error in the given expression
typeError :: (MonadError Doc m, SingI n) => UExp n -> Doc -> m a
typeError e doc = throwError $
                  doc $$ text "in the expression" <+> squotes (pretty e)

------------------------------------------------
-- The typechecker

-- | Check the given expression, aborting on type errors. The resulting
-- type and checked expression is given to the provided continuation.
-- This is parameterized over the choice of monad in order to support
-- pure operation during testing. 'StitchE' is the canonical choice for the
-- monad.

check 
  :: (MonadError Doc m, MonadReader Globals m)
  => UExp 'Zero 
  -> (forall (ty :: Type) . TypeRep ty -> Exp 'VNil ty -> m r)
  -> m r
check = go SVNil
  where
    go :: (MonadError Doc m, MonadReader Globals m, SingI n)
       => Sing (ctx :: Ctx n) 
       -> UExp n 
       -> (forall (ty :: Type) . TypeRep ty -> Exp ctx ty -> m r)
       -> m r

    go ctx (UVar i) k = check_var i ctx $ \ty v -> k ty (Var v)
      where
        check_var 
          :: Fin n 
          -> Sing (ctx :: Ctx n)
          -> (forall ty . TypeRep ty -> Elem ctx ty -> m r)
          -> m r
        check_var  FZ    (ty :%> _ ) f = f ty EZ
        check_var (FS n) (_  :%> xs) f = check_var n xs $ \ty v -> f ty (ES v)

    go _   (UGlobal s) k = do 
      globals <- ask
      lookupGlobal globals s $ \ty e -> k ty (shifts0 e)

    go ctx (ULam ty body) k
      = unpackEx ty $ \arg_ty ->
          go (arg_ty :%> ctx) body $ \res_ty body' ->
            k (arg_ty :-> res_ty) (Lam arg_ty body')

    go ctx e@(UApp e1 e2) k
      = go ctx e1 $ \fun_ty e1' ->
          go ctx e2 $ \arg_ty e2' ->
            case fun_ty of
              arg_ty' :-> res_ty
                |  Just HRefl <- arg_ty `eqTypeRep` arg_ty'
                -> k res_ty (App e1' e2')
              _ -> typeError e 
                    $ text "Bad function application." 
                   $$ indent 2 (vcat 
                        [ text "Function type:" <+> pretty fun_ty
                        , text "Argument type:" <+> pretty arg_ty ])

    go ctx (ULet rhs body) k
      = go ctx rhs $ \rhs_ty rhs' ->
          go (rhs_ty :%> ctx) body $ \body_ty body' ->
            k body_ty (Let rhs' body')

    go ctx e@(UArith e1 (UArithOp op) e2) k
      = go ctx e1 $ \ty1 e1' ->
          go ctx e2 $ \ty2 e2' ->
            case (isTypeRep @Int ty1, isTypeRep @Int ty2) of
              (Just HRefl, Just HRefl)
                -> k sing (Arith e1' op e2')
              _ -> typeError e 
                    $ text "Bad arith operand(s)." 
                   $$ indent 2 (vcat 
                        [ text " Left-hand type:" <+> pretty ty1
                        , text "Right-hand type:" <+> pretty ty2 ])

    go ctx e@(UCond e1 e2 e3) k
      = go ctx e1 $ \ty1 e1' ->
          go ctx e2 $ \ty2 e2' ->
            go ctx e3 $ \ty3 e3' ->
              case isTypeRep @Bool ty1 of
                Just HRefl
                  |  Just HRefl <- ty2 `eqTypeRep` ty3
                  -> k ty2 (Cond e1' e2' e3')
                _ -> typeError e 
                      $ text "Bad conditional." 
                     $$ indent 2 (vcat 
                          [ text "Flag type:"      <+> pretty ty1
                          , squotes (text "true")  <+> text "expression type:"
                                                   <+> pretty ty2
                          , squotes (text "false") <+> text "expression type:"
                                                   <+> pretty ty3 ])

    go ctx e@(UFix e1) k
      = go ctx e1 $ \ty1 e1' ->
          case ty1 of
            arg :-> res
              |  Just HRefl <- arg `eqTypeRep` res
              -> k arg (Fix e1')
            _ -> typeError e 
                  $ text "Bad fix over expression with type:" <+> pretty ty1

    go _   (UIntE n)  k = k sing (IntE n)
    go _   (UBoolE b) k = k sing (BoolE b)
