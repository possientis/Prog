import Data.Vector
import Statistics.Sample
import Statistics.Distribution.Poisson
import Statistics.Distribution.Normal

import qualified Statistics.Distribution as S

s1 :: Vector Double
s1 = fromList [1,2,3,4,5,6,7,8,9,10]

s2 :: PoissonDistribution
s2 = poisson 2.5

s3 :: NormalDistribution
s3 = normalDistr mean stdDev where
    mean    = 1
    stdDev  = 1


descriptive :: IO ()
descriptive = do
    print $ range s1
    -- 9.0
    print $ mean s1
    -- 5.5
    print $ stdDev s1
    --  3.0276503540974917
    print $ variance s1 
    -- 8.25
    print $ harmonicMean s1
    -- 3.414171521474055
    print $ geometricMean s1
    -- 4.528728688116765
    

discrete :: IO ()
discrete = do
    print $ S.cumulative s2 0
    -- 8.208499862389873e-2
    print $ S.mean s2 
    -- 2.5
    print $ S.variance s2
    -- 2.5
    print $ S.stdDev s2
    -- 1.5811388300841898

continuous :: IO ()
continuous = do
    print $ S.cumulative s3 0
    -- 0.15865525393145707
    print $ S.quantile s3 0.5
    print $ S.density s3 0
    print $ S.mean s3
    print $ S.variance s3
    print $ S.stdDev s3


