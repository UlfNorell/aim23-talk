
module Examples where

open import Prelude
open import Tactic.Reflection

open import Tactical
open import Intro
open import Case

S : {A B C : Set} → (A → B → C) → (A → B) → A → C
S x y z = runT (fixTac assumptionsT 10)

em : {A : Set} → ¬ ¬ Either A (¬ A)
em = intro

&&-idem : (a : Bool) → (a && a) ≡ a
&&-idem a = caseOn a then introT

cong-suc : ∀ {a b : Nat} → a ≡ b → Nat.suc a ≡ suc b
cong-suc refl = refl

infix 4 _≡N_
data _≡N_ : Nat → Nat → Set where
  zero : 0 ≡N 0
  suc  : ∀ {m n} → m ≡N n → suc m ≡N suc n

plus-0 : (n : Nat) → n + 0 ≡N n
plus-0 n = define plus-0 byInductionOn n

plus-0′ : (n : Nat) → n + 0 ≡ n
plus-0′ n = caseOn n then introT′ (hint cong-suc ∷ hint plus-0′ ∷ [])

vmap : ∀ {a b n} {A : Set a} {B : Set b} → (A → B) → Vec A n → Vec B n
vmap f xs = define vmap byInductionOn xs

append : ∀ {a n m} {A : Set a} → Vec A m → Vec A n → Vec A (m + n)
append xs ys = define append byInductionOn xs
