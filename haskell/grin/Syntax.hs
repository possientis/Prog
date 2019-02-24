import Data.Int     (Int64)
import Data.Map     (Map)
import Data.Word    (Word64)
import Data.Vector  (Vector)

import Name
import Tag
import Loc
import External

type Def       = Exp
type Alt       = Exp
type LPat      = Val
type SimpleVal = Val
type SimpleExp = Exp
type NodeSet   = Map Tag (Vector SimpleType)

data Type
    = T_SimpleType  {_simpleType  :: SimpleType }
    | T_NodeSet     {_nodeSet     :: NodeSet }
    | T_Tag         {_tagDomain   :: NodeSet }
    | T_Item        {_tagVariable :: Name 
                    ,_itemIndex   :: Int 
                    }
    deriving (Eq, Ord, Show)

data Lit 
    = LInt64  Int64
    | LWord64 Word64
    | LFloat  Float
    | LBool   Bool
    | LString String
    | LChar   Char
    deriving (Eq, Ord, Show)

data Val
    = ConstTagNode  Tag     [SimpleVal]
    | VarTagNode    Name    [SimpleVal]
    | ValTag        Tag
    | Unit
    | Lit Lit
    | Var Name
    | Undefined     Type
    deriving (Eq, Ord, Show)

data CPat
    = NodePat Tag [Name]
    | LitPat  Lit
    | DefaultPat
    | TagPat Tag
    deriving (Eq, Show, Ord)


data Exp
    = Program   [External] [Def] 
    | Def       Name [Name] Exp
    | EBind     SimpleExp LPat Exp
    | ECase     Val [Alt]
    | SApp      Name [SimpleVal]
    | SReturn   Val
    | SStore    Val
    | SFtechI   Name (Maybe Int)
    | SUpdate   Name Val
    | SBlock    Exp
    | Alt       CPat Exp
    deriving (Eq, Ord, Show)
{-
data List a = List a [a]                    -- list with at least one element

newtype Tag = Tag { unTag :: String }
newtype Var = Var { unVar :: String }

data Literal = LInt Int
             | LStr String
             | LDbl Double

data Prog = Prog (List Binding)             -- program 

data Binding = Binding Var (List Var) Exp   -- function definition

data Exp = EBind Oper LPat Exp              -- sequencing
         | ECase Val (List (CPat,Exp))      -- case
         | EOper Oper                       -- operation

data Oper = OApp Var (List SVal)            -- application
          | OUnit Val                       -- return value     
          | OStore Val                      -- allocate new heap node
          | OFetch Var (Maybe Int)          -- load heap node
          | OUpdate Var Val                 -- overwrite heap node
          | OBracket Exp


data Val = VConst Tag [SVal]                -- complete node (constant tag)
         | VVar Var [SVal]                  -- complete node (variable tag)
         | VTag Tag                         -- single tag
         | VEmpty                           -- empty
         | VSimple SVal                     -- simple value

data SVal = SLit Literal                    -- constant, basic value
          | SVar Var                        -- variable

newtype LPat = LPat { unLPat :: Val }       -- lambda pattern

data CPat = CPNode Tag [Var]                -- constant node pattern
          | CPTag Tag                       -- constant tag pattern
          | CPLit Literal                   -- constant

-}



