module GlobRegex (globToRegex, matchesGlob) where
-- fnmatch module in python

import Text.Regex.Posix ((=~))

-- fnmatch.translate in python
globToRegex :: String -> String
globToRegex cs = '^':globToRegex' cs ++ "$" -- regex is 'anchored'

-- when '^' is at the beginning of a regex, it becomes a meta-character
-- which forces any match to occur only if found at the beginning of the string
-- when '^' is not at the beginning, it is not meta, and just represents itself
-- (unless of course it is within brackets [ ])
--
-- '$' is to '^' what 'beginning' is to 'end'

globToRegex' :: String -> String
globToRegex' ""             = ""
globToRegex' ('*':cs)       = ".*" ++ globToRegex' cs
globToRegex' ('?':cs)       = '.' : globToRegex' cs
globToRegex' ('[':'!':c:cs) = "[^" ++ c : charClass cs 
globToRegex' ('[':c:cs)     = '[' : c : charClass cs 
globToRegex' ('[':_)        = error "unterminated character class"
globToRegex' (c:cs)         = escape c ++ globToRegex' cs

escape :: Char -> String
escape c  | c `elem` regexChars = '\\' : [c]
          | otherwise           = [c] 
  where regexChars = "\\+()^$.{}]|"

charClass :: String -> String
charClass (']':cs) = ']' : globToRegex' cs
charClass (c:cs) = c : charClass cs
charClass [] = error "unterminated character class"


-- foo.c : here
-- fha\kc : there

str1 = "\"fha\\\\kc\""        -- string literal
str2 = "fha\\kc"              -- string literal
bool1 = (str1 == (show str2)) -- True
str3 = read str1 :: String
bool2 = (str3 == str2)        -- True, read . show = id
str4 = show str3
bool3 = (str4 == str1)        -- True, show . read = id 

matchesGlob :: FilePath -> String -> Bool
matchesGlob name pattern = name =~ globToRegex pattern 




