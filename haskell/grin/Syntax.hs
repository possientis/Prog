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





