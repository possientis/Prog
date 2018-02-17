import System.IO

-- need to use 'Pipes' and 'Conduits' libraries
-- to solve this issue due to lazy IO 

main :: IO ()
main = do
    -- The evaluation forced by 'print' is inside
    -- the callback function and the IO will hence
    -- be forced to occur at a time when file is
    -- still open. Thus, all is good ...
    withFile "foo.txt" ReadMode $ \fd -> do
        contents <- hGetContents fd
        print contents

    -- Lazy IO will not be forced as the 'print' is 
    -- outside of the callback function.
    contents <- withFile "foo.txt" ReadMode hGetContents 
    -- *** Exception: foo.txt: hGetContents: illegal 
    -- operation (delayed read on closed handle)
    print contents
