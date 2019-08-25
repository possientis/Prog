-- Decouple parsing of format string from processing 

data Format = Number     Format
            | Str        Format
            | Lit String Format
            | End


PrintfType : Format -> Type
PrintfType (Number fmt) = (i : Int)  -> PrintfType fmt
PrintfType (Str    fmt) = (s:String) -> PrintfType fmt 
PrintfType (Lit _  fmt) =               PrintfType fmt
PrintfType End          =               String


printfFmt : (fmt : Format) -> (acc : String) -> PrintfType fmt
printfFmt (Number fmt) acc  = \i => printfFmt fmt (acc ++ show i)
printfFmt (Str fmt) acc     = \s => printfFmt fmt (acc ++ s)
printfFmt (Lit str fmt) acc =       printfFmt fmt (acc ++ str)
printfFmt End acc           = acc


toFormat : (xs : List Char) -> Format
toFormat [] = End
toFormat ('%' :: 'd' :: cs) = Number  (toFormat cs)
toFormat ('%' :: 's' :: cs) = Str     (toFormat cs)
toFormat ('%' :: cs)        = Lit "%" (toFormat cs)
toFormat (c :: cs)          = case toFormat cs of
  Lit str fmt => Lit (strCons c str) fmt
  fmt         => Lit (strCons c "")  fmt

printf : (fmt : String) -> PrintfType (toFormat (unpack fmt))
printf fmt = printfFmt _ ""


main : IO ()
main = do
  putStrLn $ printf "There are %d cats in the %s box" 5 "blue"
