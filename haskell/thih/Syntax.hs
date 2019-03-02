type Id = String

enumId :: Int -> Id
enumId n = "v" ++ show n

data Kind = Star | Kfun Kind Kind deriving Eq

data Tyvar = Tyvar Id Kind deriving Eq

data Tycon = Tycon Id Kind deriving Eq

data Type = TVar Tyvar | TCon Tycon | TAp Type Type | TGen Int deriving Eq

tUnit    :: Type 
tChar    :: Type 
tInt     :: Type 
tInteger :: Type 
tFloat   :: Type 
tDouble  :: Type 
tList    :: Type 
tArrow   :: Type 
tTuple2  :: Type 
tString  :: Type
 
tUnit    = TCon (Tycon "()" Star)
tChar    = TCon (Tycon "Char" Star)
tInt     = TCon (Tycon "Int" Star)
tInteger = TCon (Tycon "Integer" Star)
tFloat   = TCon (Tycon "Float" Star)
tDouble  = TCon (Tycon "Double" Star)
tString  = list tChar   


tList    = TCon (Tycon "[]" (Kfun Star Star))
tArrow   = TCon (Tycon "(->)" (Kfun Star (Kfun Star Star)))
tTuple2  = TCon (Tycon "(,)"  (Kfun Star (Kfun Star Star)))

infixr 4 `fn`

fn :: Type -> Type -> Type 
a `fn` b = TAp (TAp tArrow a) b

list :: Type -> Type
list a = TAp tList a

pair :: Type -> Type -> Type
pair a b = TAp (TAp tTuple2 a) b

class HasKind t where
    kind :: t -> Kind

instance HasKind Tyvar where
    kind (Tyvar _ k) = k

instance HasKind Tycon where
    kind (Tycon _ k) = k

instance HasKind Type where
    kind (TCon tycon) = kind tycon
    kind (TVar tyvar) = kind tyvar
    kind (TGen _)     = error "kind : TGen type has unknown kind" 
    kind (TAp a b)    = case kind a of 
        Kfun k1 k2   -> if kind b == k1 then k2 else error "kind : kind mismatch"
        _            -> error "kind : a is *"



