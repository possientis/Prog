import SimpleJSON

data Doc = ToBeDefined deriving Show

string :: String -> Doc
string str  = undefined  -- will type successfully

text :: String -> Doc
text str    = undefined 

double :: Double -> Doc
double num  = undefined
