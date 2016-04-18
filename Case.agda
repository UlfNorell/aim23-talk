-- Case tactic --

module Case where

open import Prelude
open import Container.Traversable
open import Tactic.Reflection

open import Tactical

solveClause : Clause → Tac ⊤
solveClause (clause _ (meta x _)) =
  do tel ← fst ∘ telView <$> liftT (inferType (meta x []))
  -| liftT₁ (inContext tel) (subgoal (meta x (teleArgs tel)) <|> liftT (typeErrorS "failed to apply tactic to rhs"))
solveClause _ = return _

solveRHS : Name → Tac ⊤
solveRHS f =
  caseM liftT (getDefinition f) of λ
  { (function cs) → _ <$ traverse solveClause cs
  ; _ → liftT (typeError (strErr "Not a function:" ∷ nameErr f ∷ [])) }

mkClause : Nat → List (Arg Type) → Name → TC Clause
mkClause x cxt c =
  do n ← visibleArity <$> getType c
  -| vpat := var "x" <$_
  -| cpat := con c (replicate n (vArg (var "y")))
  -| case splitAt x cxt of λ
     { (as , b ∷ bs) → return (clause (map vpat as ++ [ cpat <$ b ] ++ map vpat bs) unknown)
     ; _ → empty }

caseFun : Nat → List Name → Tac Name
caseFun x cs = withGoalType λ goal → liftT $
  do cxt ← getContext
  -| f   ← freshName "case-fun"
  -| declareDef (vArg f) (telPi cxt goal)
  ~| defineFun f =<< traverse (mkClause x cxt) cs
  ~| return f

caseOnT : Term → Tactical
caseOnT (var x vs) =
  do t ← liftT (inferType (var x []))
  -| case t of λ
     { (def d _) →
       do f ← caseFun x =<< liftT (getConstructors d)
       -| solveRHS f
       ~| solve ∘ def f ∘ teleArgs =<< liftT getContext
     ; _ → liftT (typeError (strErr "Cannot case on non-datatype" ∷ termErr (var x vs) ∷ strErr ":" ∷ termErr t ∷ []))
     }
caseOnT t = liftT (typeError (strErr "Cannot case on non-variable" ∷ termErr t ∷ []))

macro
  caseOn : Term → Tactic → Tactic
  caseOn = unTac ∘ caseOnT
