-- Case tactic --

module Case where

open import Prelude
open import Container.Traversable
open import Tactic.Reflection

open import Tactical


solveClause : Clause → Tac ⊤
solveClause (clause _ (meta x _)) =
  do tel ← fst ∘ telView <$> liftT (inferType (meta x []))
  -| liftT₁ (inContext tel) (
       subgoal (meta x (teleArgs tel)) <|>
       liftT (typeErrorS "failed to apply tactic to rhs"))
solveClause _ = return _

solveRHS : Name → Tac ⊤
solveRHS f =
  caseM liftT (getDefinition f) of λ where
    (function cs) → _ <$ traverse solveClause cs
    _ → liftT (typeError (strErr "Not a function:" ∷ nameErr f ∷ []))



mkClause : Nat → List (Arg Type) → Name → TC Clause
mkClause x tel c =
  do n ← visibleArity <$> getType c
  -| vpat := var "_" <$_
  -| cpat := con c (replicate n (vArg (var "_")))
  -| case splitAt (length tel - x - 1) tel of λ where
       (as , b ∷ bs) →
         return $ clause (map vpat as ++ [ cpat <$ b ] ++
                          map vpat bs) unknown
       _ → empty

caseFun : Nat → List Name → Tac Name
caseFun x cs = withGoalType λ goal → liftT $
  do tel ← reverse <$> getContext
  -| f   ← freshName "case-fun"
  -| declareDef (vArg f) (telPi tel goal)
  ~| defineFun f =<< traverse (mkClause x tel) cs
  ~| return f

caseOnT : Term → Tactical
caseOnT (var x _) =
  caseM liftT (inferType (var x [])) of λ where
    (def d _) →
      do f ← caseFun x =<< liftT (getConstructors d)
      -| solveRHS f
      ~| solve ∘ def f ∘ teleArgs ∘ reverse =<< liftT getContext
    t → liftT (typeError (strErr "Cannot case on non-datatype" ∷
                          termErr (var x []) ∷ strErr ":" ∷ termErr t ∷ []))
caseOnT t = liftT (typeError (strErr "Cannot case on non-variable" ∷ termErr t ∷ []))

open import Intro

macro
  caseOn_then_ : Term → Tactic → Tactic
  caseOn_then_ = unTac ∘ caseOnT

-- Induction --

macro
  define_byInductionOn_ : Name → Term → Tactic
  define f byInductionOn x = unTac (caseOnT x) (introT′ [ applyFun f ])

