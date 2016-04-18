
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

