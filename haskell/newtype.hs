data DataInt = D Int deriving (Eq, Ord, Show)

-- rename existing type, giving it a distinct identity
newtype NewTypeInt = N Int deriving (Eq, Ord, Show)

-- newtype has more restrictions on its uses than the data keyword
--
-- newtype => one value constructor with exactly one field
-- newtype => less runtime overhead compared to 'data'

data TwoFields = TwoFields Int Int

-- ok: exactly one field
newtype Okay = ExactlyOne Int

-- ok: type parameters are no problem
newtype Param a b = Param (Either a b)


-- ok: record syntax is fine
newtype Record = Record {
  getInt :: Int
}

-- bad: no fields
-- newtype TooFew = TooFew

-- bad: more than one field
-- newtype TooManyFields = Fields Int Int

-- bad: more than once constructor
-- newtype TooManyCtors = Bad Int | Worse Int

-- undefined remains unevaluated so no exception
example1 = case D undefined of D _  -> 1 -- example1 = 1

example2 = case undefined of D _    -> 1  -- evaluating example2 triggers exception

example3 = case N undefined of N _  -> 1  -- example3 = 1

example4 = case undefined of N _    -> 1  -- no crash !!!!

-- WHY? : there is no constructor N _ at runtime. matching against N _
-- is equivalent to matching against the wild card (_). Since the wild card
-- always matches, the expression does not need to be evaluated
--





