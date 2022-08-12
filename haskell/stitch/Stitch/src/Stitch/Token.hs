{-# LANGUAGE TupleSections  #-}

module Stitch.Token
  ( LToken  (..)
  , Token   (..)
  , noLoc
  , unArithOp
  , unBool
  , unInt
  , unLoc
  , unName
  ) where

import Text.Parsec.Pos
import Text.PrettyPrint.ANSI.Leijen

import Stitch.Op
import Stitch.Utils

-- | A lexed token
data Token
  = LParen
  | RParen
  | Lambda
  | Dot
  | ArrowTok
  | Colon
  | ArithOp UArithOp
  | IntTok Int
  | BoolTok Bool
  | If
  | Then
  | Else
  | FixTok
  | LetTok
  | InTok
  | Assign
  | Semi
  | Name String
    deriving Eq

-- | Perhaps extract a 'UArithOp'
unArithOp :: Token -> Maybe UArithOp
unArithOp (ArithOp x) = Just x
unArithOp _           = Nothing

-- | Perhaps extract an 'Int'
unInt :: Token -> Maybe Int
unInt (IntTok x) = Just x
unInt _          = Nothing

-- | Perhaps extract an 'Bool'
unBool :: Token -> Maybe Bool
unBool (BoolTok x) = Just x
unBool _           = Nothing

-- | Perhaps extract a 'String'
unName :: Token -> Maybe String
unName (Name x) = Just x
unName _        = Nothing

-- | A lexed token with location information attached
data LToken = L SourcePos Token

-- | Remove location information from an 'LToken'
unLoc :: LToken -> Token
unLoc (L _ t) = t

-- | Decorate a token with an uninformative SourcePos
noLoc :: Token -> LToken
noLoc = L (newPos "noLoc" 0 0)

instance Pretty Token where
  pretty     = getDoc . printingInfo
  prettyList = printTogether . map printingInfo

instance Show Token where
  show = render . pretty

instance Pretty LToken where
  pretty     = pretty . unLoc
  prettyList = prettyList . map unLoc

instance Show LToken where
  show = render . pretty

   -- the bools say whether or not to include a space before or a space after
type PrintingInfo = (Doc, Bool, Bool)

alone :: Doc -> PrintingInfo
alone = (, True, True)

getDoc :: PrintingInfo -> Doc
getDoc (doc, _, _) = doc

printingInfo :: Token -> PrintingInfo
printingInfo LParen          = (char '(', True, False)
printingInfo RParen          = (char ')', False, True)
printingInfo Lambda          = (char '\\', True, False)
printingInfo Dot             = (char '.', False, True)
printingInfo ArrowTok        = alone $ text "->"
printingInfo Colon           = (char ':', False, False)
printingInfo (ArithOp a)     = alone $ pretty a
printingInfo (IntTok i)      = alone $ int i
printingInfo (BoolTok True)  = alone $ text "true"
printingInfo (BoolTok False) = alone $ text "false"
printingInfo If              = alone $ text "if"
printingInfo Then            = alone $ text "then"
printingInfo Else            = alone $ text "else"
printingInfo FixTok          = alone $ text "fix"
printingInfo LetTok          = alone $ text "let"
printingInfo InTok           = alone $ text "in"
printingInfo Assign          = alone $ text "="
printingInfo Semi            = (char ';', False, True)
printingInfo (Name t)        = alone $ text t

printTogether :: [PrintingInfo] -> Doc
printTogether []  = empty
printTogether pis = getDoc $ foldl1 combine pis
  where
    combine (doc1, before_space, inner_space1) (doc2, inner_space2, after_space)
      | inner_space1 && inner_space2
      = (doc1 <+> doc2, before_space, after_space)

      | otherwise
      = (doc1 <> doc2, before_space, after_space)
