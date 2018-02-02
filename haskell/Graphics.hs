import Diagrams.Prelude
import Diagrams.Backend.SVG.CmdLine

-- ghc Graphics.hs -o a.out; ./a.out -w 256 -h 256 -o diagram.svg;
-- gimp diagram.svg &


sierpinski :: Int -> Diagram SVG
sierpinski 1 = eqTriangle 1
sierpinski n = 
        s
       ===
    (s ||| s) # centerX
    where
    s = sierpinski (n - 1)


example :: Diagram SVG
example = sierpinski 5 # fc black


main :: IO ()
main = defaultMain example

   
