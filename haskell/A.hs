import System.Environment
import Text.Printf

-- ghc A.hs -rtsopts 
-- so as to allow RTS options

-- -K1000000000 increases stack size to 1G
-- -sstderr tells run time to print stats on stderr

-- ./A 1e7 +RTS -sstderr -K1000000000


{-
5000000.5
   2,572,814,560 bytes allocated in the heap
   2,729,851,888 bytes copied during GC
     888,606,224 bytes maximum residency (12 sample(s))
      76,694,376 bytes maximum slop
            1714 MB total memory in use (0 MB lost due to fragmentation)

                                    Tot time (elapsed)  Avg pause  Max pause
  Gen  0      4300 colls,     0 par    3.76s    3.77s     0.0009s    0.6974s
  Gen  1        12 colls,     0 par    3.73s    3.75s     0.3124s    1.7004s

  INIT    time    0.00s  (  0.00s elapsed)
  MUT     time    1.90s  (  1.89s elapsed)
  GC      time    7.49s  (  7.52s elapsed)
  EXIT    time    0.13s  (  0.14s elapsed)
  Total   time    9.53s  (  9.55s elapsed)

  %GC     time      78.7%  (78.7% elapsed)

  Alloc rate    1,355,597,438 bytes per MUT second

  Productivity  21.3% of total user, 21.3% of total elapsed

-}

-- In order to calculate the mean of 10 million numbers, the program requiresd
-- 2.5G of heap memory and spent 80% of its time garbage collecting
--
main = do
  [d] <- map read `fmap` getArgs
  printf "%f\n" (mean [1..d])



mean :: [Double] -> Double
mean xs = sum xs / fromIntegral (length xs)



