{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeInType       #-}
module Stitch.Parse
  ( parseExp
  , parseExpM
  , parseStmt
  , parseStmtM
  , parseStmts
  , parseStmtsM
  ) where

import Control.Applicative
import Control.Arrow                    hiding ((<+>))
import Control.Monad.Reader
import Text.Parsec.Combinator
import Text.Parsec.Pos
import Text.Parsec.Prim                 hiding (parse, (<|>))
import Text.PrettyPrint.ANSI.Leijen     hiding ((<$>))


import Stitch.Control.Monad.HReader
import Stitch.Data.Nat
import Stitch.Data.Vec
import Stitch.Op
import Stitch.Monad
import Stitch.Statement
import Stitch.Token
import Stitch.Type
import Stitch.Unchecked
import Stitch.Utils

-- | Parse a sequence of semicolon-separated statements, aborting with
-- an error upon failure
parseStmtsM :: [LToken] -> StitchE [Statement]
parseStmtsM = eitherToStitchE . parseStmts

-- | Parse a sequence of semicolon-separated statements
parseStmts :: [LToken] -> Either String [Statement]
parseStmts = parse stmts

-- | Parse a 'Statement', aborting with an error upon failure
parseStmtM :: [LToken] -> StitchE Statement
parseStmtM = eitherToStitchE . parseStmt

-- | Parse a 'Statement'
parseStmt :: [LToken] -> Either String Statement
parseStmt = parse stmt

-- | Parse a 'UExp', aborting with an error upon failure
parseExpM :: [LToken] -> StitchE (UExp 'Zero)
parseExpM = eitherToStitchE . parseExp

-- | Parse a 'UExp'
parseExp :: [LToken] -> Either String (UExp 'Zero)
parseExp = parse expr

parse :: Parser 'Zero a -> [LToken] -> Either String a
parse p ts
  = left show 
  $ runReader (runParserT (p <* eof) () "" ts) VNil


----------------------
-- Plumbing

-- A parser usable in a context with n bound variables
-- the "state" is a list of bound names. searching a bound name in the list
-- gives you the correct deBruijn index
type Parser n a = ParsecT [LToken] () (Reader (Vec String n)) a

-- | Bind a name over an expression
bind :: String -> Parser ('Succ n) a -> Parser n a
bind v body = hlocal f body
  where
    f :: Vec String n -> Vec String ('Succ n)
    f = (v :>)

-- | Parse the given nullary token
tok :: Token -> Parser n ()
tok t = tokenPrim (render . pretty) next_pos (guard . (t ==) . unLoc)

-- | Parse the given unary token
tok' :: (Token -> Maybe thing) -> Parser n thing
tok' matcher = tokenPrim (render . pretty) next_pos (matcher . unLoc)

-- | Parse one of a set of 'ArithOp's
arith_op :: [UArithOp] -> Parser n UArithOp
arith_op ops = tokenPrim 
  (render . pretty) 
  next_pos
  (\case 
    L _ (ArithOp op) | op `elem` ops -> Just op
    _                                -> Nothing
  )

next_pos 
  :: SourcePos  -- ^ position of the current token
  -> LToken     -- ^ current token
  -> [LToken]   -- ^ remaining tokens
  -> SourcePos  -- ^ location of the next token
next_pos pos _ []            = pos
next_pos _   _ (L pos _ : _) = pos

--------------
-- Real work

stmts :: Parser 'Zero [Statement]
stmts = stmt `sepEndBy` tok Semi

stmt :: Parser 'Zero Statement
stmt = choice 
  [ try $ NewGlobal <$> tok' unName <* tok Assign <*> expr
  , BareExp <$> expr 
  ]

expr :: Parser n (UExp n)
expr = choice 
  [ lam
  , cond
  , let_exp
  , int_exp `chainl1` bool_op 
  ]

int_exp :: Parser n (UExp n)
int_exp = term `chainl1` add_op

term :: Parser n (UExp n)
term = apps `chainl1` mul_op

apps :: Parser n (UExp n)
apps = choice 
  [ UFix <$ tok FixTok <*> expr
  , foldl1 UApp <$> some factor 
  ]

factor :: Parser n (UExp n)
factor = choice 
  [ between (tok LParen) (tok RParen) expr
  , UIntE <$> tok' unInt
  , UBoolE <$> tok' unBool
  , var 
  ]

lam :: Parser n (UExp n)
lam = do
  tok Lambda
  bound_var <- tok' unName
  tok Colon
  typ <- ty
  tok Dot
  e <- bind bound_var $ expr
  return (ULam typ e)

cond :: Parser n (UExp n)
cond = UCond <$ tok If <*> expr <* tok Then <*> expr <* tok Else <*> expr

let_exp :: Parser n (UExp n)
let_exp = do
  tok LetTok
  bound_var <- tok' unName
  tok Assign
  rhs <- expr
  tok InTok
  body <- bind bound_var $ expr
  return (ULet rhs body)

var :: Parser n (UExp n)
var = do
  n <- tok' unName
  m_index <- asks (elemIndex n)
  case m_index of
    Nothing -> return (UGlobal n)
    Just i  -> return (UVar i)

add_op  :: Parser n (UExp n -> UExp n -> UExp n)
mul_op  :: Parser n (UExp n -> UExp n -> UExp n)
bool_op :: Parser n (UExp n -> UExp n -> UExp n)

add_op  = mk_op <$> arith_op [uPlus, uMinus]
mul_op  = mk_op <$> arith_op [uTimes, uDivide, uMod]
bool_op = mk_op <$> arith_op [uLess, uLessE, uGreater, uGreaterE, uEquals]

mk_op :: UArithOp -> UExp n -> UExp n -> UExp n
mk_op op = \e1 e2 -> UArith e1 op e2

----------------------------------------
-- Types

ty :: Parser n Ty
ty = chainr1 arg_ty (arrX <$ tok ArrowTok)
  where
    arrX :: Ty -> Ty -> Ty
    arrX (Ty arg) (Ty res) = Ty (arg :-> res)

arg_ty :: Parser n Ty
arg_ty = choice 
  [ between (tok LParen) (tok RParen) ty
  , tycon 
  ]

tycon :: Parser n Ty
tycon = do
  n <- tok' unName
  case n of
    "Int" -> return (mkTy @Int)
    "Bool" -> return (mkTy @Bool)
    _      -> unexpected $ render $
              text "type name" <+> squotes (text n)

