
module Tactical where

open import Prelude
open import Tactic.Reflection

Tactical = Tactic → Tactic

fixTac : Tactical → Nat → Tactic
fixTac f zero _ = typeErrorS "Search depth exhausted"
fixTac f (suc depth) = f (fixTac f depth)

tryAll : List Tactical → Tactical
tryAll tacs rec hole = choice (map (λ tac → tac rec hole) tacs)

guardT : (Term → Bool) → Tactical
guardT ok rec hole =
  do rec hole
  ~| v ← normalise hole
  -| guardA! (ok v) (return _)

record Tac {a} (A : Set a) : Set a where
  no-eta-equality
  constructor mkTac
  field runTac : Tactic → Term → TC A

open Tac public

instance
  FunctorTac : ∀ {a} → Functor {a} Tac
  fmap {{FunctorTac}} f (mkTac t) = mkTac λ rec hole → fmap f (t rec hole)

  FunctorTac′ : ∀ {a} → Functor′ {a} Tac
  fmap′ {{FunctorTac′}} f (mkTac t) = mkTac λ rec hole → fmap f (t rec hole)

  ApplicativeTac : ∀ {a} → Applicative {a} Tac
  pure  {{ApplicativeTac}} x = mkTac λ _ _ → pure x
  _<*>_ {{ApplicativeTac}} (mkTac f) (mkTac x) = mkTac λ rec hole → f rec hole <*> x rec hole

  ApplicativeTac′ : ∀ {a} → Applicative′ {a} Tac
  _<*>′_ {{ApplicativeTac′}} (mkTac f) (mkTac x) = mkTac λ rec hole → f rec hole <*> x rec hole

  MonadTac : ∀ {a} → Monad {a} Tac
  return {{MonadTac}} = pure
  _>>=_  {{MonadTac}} (mkTac m) f = mkTac λ rec hole → m rec hole >>= λ x → runTac (f x) rec hole

  MonadTac′ : ∀ {a} → Monad′ {a} Tac
  _>>=′_  {{MonadTac′}} (mkTac m) f = mkTac λ rec hole → m rec hole >>= λ x → runTac (f x) rec hole

currentGoal : Tac Term
currentGoal = mkTac λ _ hole → return hole

liftT : ∀ {a} {A : Set a} → TC A → Tac A
liftT m = mkTac λ _ _ → m

goalType : Tac Type
goalType = liftT ∘ inferType =<< currentGoal

solveSubGoal : Term → Tac ⊤
solveSubGoal hole = mkTac λ rec _ → rec hole
