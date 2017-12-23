import Control.Monad
import System.Random
import Control.Monad.Trans.State


type GeneratorState = State StdGen

rollDie :: GeneratorState Int
rollDie = do 
  generator <- get
  let (value, newGenerator) = randomR (1,6) generator
  put newGenerator
  return value

rollDice :: GeneratorState (Int, Int)
rollDice = liftM2 (,) rollDie rollDie


rollNDice :: Int -> GeneratorState [Int]
rollNDice n = sequence $ replicate n rollDie

getRandom :: Random a => GeneratorState a
getRandom = do
  generator <- get
  let (value, newGen) = random generator
  put newGen
  return value

allTypes :: GeneratorState (Int, Float, Char, Integer, Double, Bool, Int)
allTypes = liftM (,,,,,,) getRandom
                    `ap`  getRandom
                    `ap`  getRandom
                    `ap`  getRandom
                    `ap`  getRandom
                    `ap`  getRandom
                    `ap`  getRandom
