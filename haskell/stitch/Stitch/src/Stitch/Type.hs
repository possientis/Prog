{-# OPTIONS_GHC -Wno-missing-pattern-synonym-signatures #-}
{-# OPTIONS_GHC -Wno-orphans                            #-}
{-# LANGUAGE AllowAmbiguousTypes                        #-}
{-# LANGUAGE FlexibleInstances                          #-}
{-# LANGUAGE GADTs                                      #-}
{-# LANGUAGE PatternSynonyms                            #-}
{-# LANGUAGE RankNTypes                                 #-}
{-# LANGUAGE ScopedTypeVariables                        #-}
{-# LANGUAGE TypeApplications                           #-}
{-# LANGUAGE TypeFamilies                               #-}
{-# LANGUAGE TypeInType                                 #-}
{-# LANGUAGE TypeOperators                              #-}
{-# LANGUAGE ViewPatterns                               #-}

module  Stitch.Type
  ( pattern Ty
  , pattern (:->)
  , pattern (:@:)
  , Ty
  , extractArgType
  , extractResType
  , isTypeRep 
  , mkTy
  ) where

import Data.Kind
import Data.Maybe
import Type.Reflection
import Text.PrettyPrint.ANSI.Leijen

import Stitch.Data.Exists
import Stitch.Data.Singletons

import Stitch.Utils

type Ty = Ex (TypeRep :: Type -> Type)

pattern Ty t = Ex t
{-# COMPLETE Ty #-}

mkTy :: forall (a :: Type) . Typeable a => Ty
mkTy = Ty (typeRep @a)

instance Eq Ty where
  Ty a == Ty b = isJust (a `eqTypeRep` b)

-- This simple pattern definition will lead to type checking failure
-- in the Check module. The definition below appears to be required.
-- pattern arg :-> res = Fun arg res 

pattern arg :-> res <- (checkFun -> FunOnTypes arg res)
  where
    arg :-> res = arg `Fun` res

data CheckFun fun where
  FunOnTypes 
    :: forall (arg :: Type) (res :: Type)
     . TypeRep arg 
    -> TypeRep res 
    -> CheckFun (arg -> res)
  OtherType :: CheckFun fun

checkFun :: TypeRep fun -> CheckFun fun
checkFun (arg `Fun` res)
  | Just HRefl <- typeRepKind arg `eqTypeRep` typeRep @Type
  , Just HRefl <- typeRepKind res `eqTypeRep` typeRep @Type
  = FunOnTypes arg res
checkFun _other = OtherType


extractArgType 
  :: forall (arg :: Type) (res :: Type)
   . TypeRep (arg -> res) 
  -> TypeRep arg
extractArgType (arg `Fun` _)       = arg
extractArgType (App (App _ arg) _) = arg

extractResType 
  :: forall (arg :: Type) (res :: Type)
   . TypeRep (arg -> res) 
  -> TypeRep res
extractResType (_ `Fun` res) = res
extractResType (App _ res)   = res

pattern f :@: a = f `App` a

isTypeRep :: forall a b. Typeable a => TypeRep b -> Maybe (a :~~: b)
isTypeRep = eqTypeRep (typeRep @a)

-- Sing instance for types
instance SingKind Type where
  type Sing = TypeRep

  fromSing _ = error "no term-level Types"

instance Typeable (a :: Type)  => SingI a where
  sing = typeRep

_castTo :: forall a b . Typeable a => a -> TypeRep b -> Maybe b
_castTo x repB = case isTypeRep @a repB of
  Just HRefl  -> Just x
  Nothing     -> Nothing

instance Pretty Ty where
  pretty (Ty ty) = pretty_ty topPrec ty

instance Pretty (TypeRep ty) where
  pretty = pretty_ty topPrec

arrowLeftPrec   :: Precedence
arrowRightPrec  :: Precedence
arrowPrec       :: Precedence
arrowLeftPrec   = 5
arrowRightPrec  = 4.9
arrowPrec       = 5

pretty_ty :: Precedence -> TypeRep ty -> Doc
pretty_ty prec (arg `Fun` res) 
  = maybeParens (prec >= arrowPrec) 
  $ hsep [ pretty_ty arrowLeftPrec arg
         , text "->"
         , pretty_ty arrowRightPrec res 
         ]
pretty_ty _ other = text (show other)
