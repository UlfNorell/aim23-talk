
module Tactical where

open import Prelude
open import Container.Traversable
open import Tactic.Reflection

record Tac {a} (A : Set a) : Set a where
  no-eta-equality
  constructor mkTac
  field unTac : Tactic → Term → TC A

open Tac public

-- Boring instances --

instance
  FunctorTac : ∀ {a} → Functor {a} Tac
  fmap {{FunctorTac}} f (mkTac t) = mkTac λ rec hole → fmap f (t rec hole)

  FunctorTac′ : ∀ {a b} → Functor′ {a} {b} Tac
  fmap′ {{FunctorTac′}} f (mkTac t) = mkTac λ rec hole → fmap′ f (t rec hole)

  ApplicativeTac : ∀ {a} → Applicative {a} Tac
  pure  {{ApplicativeTac}} x = mkTac λ _ _ → pure x
  _<*>_ {{ApplicativeTac}} (mkTac f) (mkTac x) = mkTac λ rec hole → f rec hole <*> x rec hole

  ApplicativeTac′ : ∀ {a b} → Applicative′ {a} {b} Tac
  _<*>′_ {{ApplicativeTac′}} (mkTac f) (mkTac x) = mkTac λ rec hole → f rec hole <*>′ x rec hole

  MonadTac : ∀ {a} → Monad {a} Tac
  return {{MonadTac}} = pure
  _>>=_  {{MonadTac}} (mkTac m) f = mkTac λ rec hole → m rec hole >>= λ x → unTac (f x) rec hole

  MonadTac′ : ∀ {a b} → Monad′ {a} {b} Tac
  _>>=′_  {{MonadTac′}} (mkTac m) f = mkTac λ rec hole → m rec hole >>=′ λ x → unTac (f x) rec hole

  AlternativeTac : ∀ {a} → Alternative {a} Tac
  empty {{AlternativeTac}} = mkTac λ _ _ → empty
  _<|>_ {{AlternativeTac}} (mkTac t) (mkTac t₁) = mkTac λ rec hole → t rec hole <|> t₁ rec hole

-- Some operations --

currentGoal : Tac Term
currentGoal = mkTac λ _ hole → return hole

liftT : ∀ {a} {A : Set a} → TC A → Tac A
liftT m = mkTac λ _ _ → m

liftT₁ : ∀ {a b} {A : Set a} {B : Set b} → (TC A → TC B) → Tac A → Tac B
liftT₁ f (mkTac t) = mkTac λ rec hole → f (t rec hole)

goalType : Tac Type
goalType = liftT ∘ inferType =<< currentGoal

withGoalType : ∀ {a} {A : Set a} → (Type → Tac A) → Tac A
withGoalType tac = goalType >>=′ tac

solve : Term → Tac ⊤
solve v = liftT ∘ unify v =<< currentGoal

subgoal : Term → Tac ⊤
subgoal hole = mkTac λ rec _ → rec hole

Tactical = Tac ⊤

-- Solve the current goal with `tm` (of type `t`) applied
-- to subgoals for its visible arguments.
apply : (List (Arg Term) → Term) → Type → Tactical
apply tm t =
  do vs ← replicateA (visibleArity t) (liftT newMeta!)
  -| solve (tm (map vArg vs))
  ~| _ <$ traverse subgoal (reverse vs)

fixTac : Tactical → Nat → Tactic
fixTac f zero _ = typeErrorS "Search depth exhausted"
fixTac f (suc depth) = unTac f (fixTac f depth)
