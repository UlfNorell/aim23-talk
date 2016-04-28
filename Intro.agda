-- Intro tactic --

module Intro where

open import Prelude
open import Container.Traversable
open import Container.List
open import Tactic.Reflection

open import Tactical
open import Utils

-- Assumptions --

applyVar : Nat → Arg Type → Tactical
applyVar x t = apply (var x) (unArg t)

assumptionsT : Tactical
assumptionsT =
  do cxt ← liftT getContext
  -| choice (mapWithIndex applyVar cxt)

-- Solve with constructor --

applyCon : Name → Tactical
applyCon c = apply (con c) =<< liftT (getType c)

applyCons : Type → Tactical
applyCons (def d _) =
  choice ∘ map applyCon =<< liftT (getConstructors d)
applyCons _ = empty

constructorsT = withGoalType applyCons

ex₂ : Vec Bool 3
ex₂ = runT (fixTac constructorsT 10)

ex₃ : {A : Set} → A → Vec A 3
ex₃ x = runT (fixTac (choice (assumptionsT ∷ constructorsT ∷ [])) 10)

-- Introduce lambdas --

tryAbsurdLambda : Arg Type → Tactical
tryAbsurdLambda a = solve (pat-lam (absurd-clause ((absurd <$ a) ∷ []) ∷ []) [])

introLam : Type → Tactical
introLam (pi a b) =
  tryAbsurdLambda a <|>
  ( do m ← liftT (extendContext a (newMeta (unAbs b)))
    -| solve (lam (getVisibility a) (m <$ b))
    ~| liftT₁ (extendContext a) (subgoal m) )
introLam _ = empty

lambdaT = withGoalType introLam

-- Combining everything --

introTactic′ : List Tactical → Nat → Tactic
introTactic′ hints =
  fixTac $ choice $ lambdaT
                  ∷ assumptionsT
                  ∷ constructorsT
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

-- Try to apply a given function --

applyFun : Name → Tactical
applyFun f = apply (def f) =<< liftT (getType f)

macro
  hint : Name → Tactic
  hint x = give (def₁ (quote applyFun) (lit (name x)))
