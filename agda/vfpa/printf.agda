module printf where

open import IO
open import Agda.Builtin.Unit
open import Data.Nat
open import Data.Nat.Show   as Nat
open import Data.Char
open import Data.List
open import Data.String     hiding (_++_)

data Format-d : Set where
  Format-Nat    : Format-d → Format-d
  Format-String : Format-d → Format-d
  Not-Format    : (c : Char) → Format-d → Format-d
  Empty-Format  : Format-d

format-cover : List Char → Format-d
format-cover ('%' ∷ 'n' ∷ cs) = Format-Nat (format-cover cs)
format-cover ('%' ∷ 's' ∷ cs) = Format-String (format-cover cs)
format-cover (c ∷ cs) = Not-Format c (format-cover cs)
format-cover [] = Empty-Format

format-th : Format-d → Set
format-th (Format-Nat f)    = ℕ → format-th f
format-th (Format-String f) = String → format-th f
format-th (Not-Format c f)  = format-th f
format-th Empty-Format      = String

format-t : String → Set
format-t s = format-th (format-cover (toList s))


format-h : List Char → (d : Format-d) → format-th d
format-h s (Format-Nat f)    = λ n → format-h (s ++ toList (Nat.show n)) f
format-h s (Format-String f) = λ t → format-h (s ++ (toList t)) f
format-h s (Not-Format c f)  = format-h (s ++ (c ∷ [])) f
format-h s Empty-Format      = fromList s

format : (f : String) → format-t f
format f = format-h [] (format-cover (toList f))

-- $ agda --compile printf.agda
main = run do
  putStrLn (format "%n of the %ss are in the %s %s" 25 "dog" "toasty" "doghouse")
