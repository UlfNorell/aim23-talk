
module Utils where

open import Prelude

mapWithIndex : {A B : Set} → (Nat → A → B) → List A → List B
mapWithIndex f xs = vecToList (f <$> tabulate finToNat <*> listToVec xs)
