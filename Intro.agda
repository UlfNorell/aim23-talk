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
tryApply tm t =
  do vs ← replicateA (visibleArity t) (liftT newMeta!)
  -| solve (tm (map vArg vs))
  ~| _ <$ traverse subgoal (reverse vs)

tryFun : Name → Tactical
tryFun f = tryApply (def f) =<< liftT (getType f)

tryRecFun : Name → Tactical
tryRecFun f = onSubgoals (guardT (not ∘ isCon)) (tryFun f)

tryConstructor : Name → Tactical
tryConstructor c = tryApply (con c) =<< liftT (getType c)

tryConstructors : Type → Tactical
tryConstructors (def d _) =
  choice ∘ map tryConstructor =<< liftT (getConstructors d)
tryConstructors _ = empty

tryVariable : Nat → Arg Type → Tactical
tryVariable x t = tryApply (var x) (unArg t)

tryVariables : Tactical
tryVariables =
  do cxt ← liftT getContext
  -| choice (mapWithIndex tryVariable cxt)

tryAbsurdLambda : Arg Type → Tactical
tryAbsurdLambda a = solve (pat-lam (absurd-clause ((absurd <$ a) ∷ []) ∷ []) [])

tryLambda : Type → Tactical
tryLambda (pi a b) =
  tryAbsurdLambda a <|>
  ( do m ← liftT (extendContext a (newMeta (unAbs b)))
    -| solve (lam (getVisibility a) (m <$ b))
    ~| liftT₁ (extendContext a) (subgoal m) )
tryLambda _ = empty

introTactic′ : List Tactical → Nat → Tactic
introTactic′ hints =
  runTac $ choice $ withGoalType tryLambda
                  ∷ tryVariables
                  ∷ withGoalType tryConstructors
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
