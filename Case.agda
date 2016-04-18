-- Case tactic --

module Case where

open import Prelude
open import Container.Traversable
open import Tactic.Reflection

applyToClause : Tactic → Clause → TC ⊤
applyToClause tac (clause _ (meta x _)) =
  do tel ← fst ∘ telView <$> inferType (meta x [])
  -| inContext tel (tac (meta x (teleArgs tel)) <|> typeErrorS "failed to apply tactic to rhs")
applyToClause _ _ = return _

applyToRHS : Tactic → Name → TC ⊤
applyToRHS tac f =
  caseM getDefinition f of λ
  { (function cs) → _ <$ traverse (applyToClause tac) cs
  ; _ → typeError (strErr "Not a function:" ∷ nameErr f ∷ []) }

mkClause : Nat → List (Arg Type) → Name → TC Clause
mkClause x cxt c =
  do n ← visibleArity <$> getType c
  -| vpat := var "x" <$_
  -| cpat := con c (replicate n (vArg (var "y")))
  -| case splitAt x cxt of λ
     { (as , b ∷ bs) → return (clause (map vpat as ++ [ cpat <$ b ] ++ map vpat bs) unknown)
     ; _ → empty }

caseFun : Nat → Type → List Name → TC Name
caseFun x goal cs =
  do cxt ← getContext
  -| f   ← freshName "case-fun"
  -| declareDef (vArg f) (telPi cxt goal)
  ~| defineFun f =<< traverse (mkClause x cxt) cs
  ~| return f

caseOnT : Term → Tactic → Tactic
caseOnT (var x vs) tac hole =
  do t    ← inferType (var x [])
  -| goal ← inferType hole
  -| case t of λ
     { (def d _) →
       do f ← caseFun x goal =<< getConstructors d
       -| applyToRHS tac f
       ~| unify hole ∘ def f ∘ teleArgs =<< getContext
     ; _ → typeError (strErr "Cannot case on non-datatype" ∷ termErr (var x vs) ∷ strErr ":" ∷ termErr t ∷ [])
     }
caseOnT t _ _ = typeError (strErr "Cannot case on non-variable" ∷ termErr t ∷ [])

macro
  caseOn : Term → Tactic → Tactic
  caseOn = caseOnT
