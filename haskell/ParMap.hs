import Control.Parallel (par, pseq)

-- ghc source -threaded -o executable
-- ./executable +RTS -N4 (select four processors at runtime)

parallelMap :: (a -> b) -> [a] -> [b]
parallelMap f (x:xs)  = let r = f x in r `par` r : parallelMap f xs
parallelMap _ _       = []


forceList :: [a] -> ()
forceList (x:xs) = x `pseq` forceList xs
forceList _      = ()

stricterMap :: (a -> b) -> [a] -> [b]
stricterMap f xs = forceList xs `seq` map f xs

forceListAndElts :: (a -> ()) -> [a] -> ()
forceListAndElts forceElt (x:xs) =
  forceElt x `seq` forceListAndElts forceElt xs
forceListAndElts _ _ = ()




