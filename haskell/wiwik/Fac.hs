module Fac (fac) where

fac :: Int -> Int -> Int
fac a 0 = a
fac a n = fac (n*a) (n-1)

{- core : -ddump-simpl
Rec {
fac :: Int -> Int -> Int
fac = \ (a :: Int) (ds :: Int) ->
    case ds of wild_X8 { I# ds1 ->
        case ds1 of _ {
            __DEFAULT ->
                fac (* @ Int $fNumInt wild_X8 a)
                    (- @ Int $fNumInt wild_X8 (I# 1#));
            0# -> a
        }
    }
end Rec }
-}

{- STG : --ddump-stg
Fac.fac [Occ=LoopBreaker]
  :: GHC.Types.Int -> GHC.Types.Int -> GHC.Types.Int
[GblId, Arity=2, Str=DmdType, Unf=OtherCon []] =
    \r srt:SRT:[r1 :-> Fac.fac, rw5 :-> GHC.Num.$fNumInt] [a_s1EM
                                                           ds_s1EN]
        case ds_s1EN of wild_s1EO {
          GHC.Types.I# ds1_s1EP [Occ=Once!] ->
              case ds1_s1EP of _ [Occ=Dead] {
                __DEFAULT ->
                    let {
                      sat_s1ET [Occ=Once] :: GHC.Types.Int
                      [LclId, Str=DmdType] =
                          \u srt:SRT:[rw5 :-> GHC.Num.$fNumInt] []
                              let {
                                sat_s1ES [Occ=Once] :: GHC.Types.Int
                                [LclId, Str=DmdType] =
                                    NO_CCS GHC.Types.I#! [1#];
                              } in  GHC.Num.- GHC.Num.$fNumInt wild_s1EO sat_s1ES; } in
                    let {
                      sat_s1ER [Occ=Once] :: GHC.Types.Int
                      [LclId, Str=DmdType] =
                          \u srt:SRT:[rw5 :-> GHC.Num.$fNumInt] []
                              GHC.Num.* GHC.Num.$fNumInt wild_s1EO a_s1EM;
                    } in  Fac.fac sat_s1ER sat_s1ET;
                0# -> a_s1EM;
              };
        };
-}
