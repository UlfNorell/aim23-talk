-- Intro tactic --

module Intro where

open import Prelude
open import Container.Traversable
open import Tactic.Reflection

open import Tactical

mapWithIndex : {A B : Set} → (Nat → A → B) → List A → List B
mapWithIndex f xs = vecToList (f <$> tabulate finToNat <*> listToVec xs)

isCon : Term → Bool
isCon (con _ _) = true
isCon _ = false

tryApply : (List (Arg Term) → Term) → Type → Tactical
tryApply tm t rec hole =
  do vs ← replicateA (visibleArity t) newMeta!
  -| unify hole (tm (map vArg vs))
  ~| _ <$ traverse rec (reverse vs)

tryFun : Name → Tactical
tryFun f rec hole =
  do t ← getType f
  -| tryApply (def f) t rec hole

tryRecFun : Name → Tactical
tryRecFun f = tryFun f ∘ guardT (not ∘ isCon)

tryConstructor : Name → Tactical
tryConstructor c rec hole = (λ t → tryApply (con c) t rec hole) =<< getType c

tryConstructors : Type → Tactical
tryConstructors (def d _) rec hole =
  choice ∘ map (λ c → tryConstructor c rec hole) =<< getConstructors d
tryConstructors _ _ _ = empty

tryVariable : Nat → Type → Tactical
tryVariable x t = tryApply (var x) t

tryVariables : Tactical
tryVariables rec hole =
  do cxt ← getContext
  -| choice (mapWithIndex (λ i t → tryVariable i (unArg t) rec hole) cxt)

tryAbsurdLambda : Arg Type → Tactic
tryAbsurdLambda a hole = unify hole (pat-lam (absurd-clause ((absurd <$ a) ∷ []) ∷ []) [])

tryLambda : Type → Tactical
tryLambda (pi a b) rec hole =
  tryAbsurdLambda a hole <|>
  ( do m ← extendContext a (newMeta (unAbs b))
    -| unify hole (lam (getVisibility a) (m <$ b))
    ~| extendContext a (rec m) )
tryLambda _ _ _ = empty

typedTactical : (Type → Tactical) → Tactical
typedTactical tac rec hole =
  do goal ← inferType hole
  -| tac goal rec hole

introTactic′ : List Tactical → Nat → Tactic
introTactic′ hints =
  fixTac $ tryAll $ typedTactical tryLambda
                  ∷ tryVariables
                  ∷ typedTactical tryConstructors
                  ∷ hints

introTactic : Nat → Tactic
introTactic = introTactic′ []

introT = introTactic 20

introT′ : List Tactical → Tactic
introT′ tacs = introTactic′ tacs 20

macro
  intro : Tactic
  intro = introT

  intro′ : List Tactical → Tactic
  intro′ = introT′

  hint : Name → Tactic
  hint x = give (def₁ (quote tryFun) (lit (name x)))

  ih : Name → Tactic
  ih x = give (def₁ (quote tryRecFun) (lit (name x)))
