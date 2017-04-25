data Expr
  = BoolExpr Bool
  | IfExpr Expr Expr Expr
  | Zero
  | Succ Expr
  | Pred Expr
  | IsZero Expr


evaluate :: Expr -> Maybe Expr
evaluate (BoolExpr b) = return $ BoolExpr b
evaluate (IfExpr cond cons alter) = do
  condition <- evaluate cond
  case condition of
    BoolExpr b ->
      if b then evaluate cons else evaluate alter
    _          -> Nothing
evaluate (Zero) = return $ Zero
evaluate (Succ expr)  = do
  value <- evaluate expr
  case value of 
    (Zero)      -> return $ Succ Zero
    y@(Succ x)  -> return $ Succ y
    _           -> Nothing
evaluate (Pred expr) = do
  value <- evaluate expr
  case value of 
      (Succ x)  -> return x
      _         -> Nothing
evaluate (IsZero expr) = do
  value <- evaluate expr
  case value of 
    (Zero)    -> return $ BoolExpr True
    (Succ x)  -> return $ BoolExpr False
    _         -> Nothing


