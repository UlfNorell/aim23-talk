
module Examples where

open import Prelude

open import Intro
open import Case

em : {A : Set} → ¬ ¬ Either A (¬ A)
em = intro

&&-idem : (a : Bool) → (a && a) ≡ a
&&-idem a = caseOn a introT

cong-suc : ∀ {a b : Nat} → a ≡ b → Nat.suc a ≡ suc b
cong-suc refl = refl

infix 4 _≡N_
data _≡N_ : Nat → Nat → Set where
  zero : 0 ≡N 0
  suc  : ∀ {m n} → m ≡N n → suc m ≡N suc n

plus-0 : (n : Nat) → n + 0 ≡N n
plus-0 n = caseOn n (introT′ (ih plus-0 ∷ []))

plus-0′ : (n : Nat) → n + 0 ≡ n
plus-0′ n = caseOn n (introT′ (hint cong-suc ∷ ih plus-0′ ∷ []))
