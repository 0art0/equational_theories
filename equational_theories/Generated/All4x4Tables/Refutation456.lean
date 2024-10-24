
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,3,3,1],[3,3,3,3],[0,0,0,0],[2,0,2,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,3,3,1],[3,3,3,3],[0,0,0,0],[2,0,2,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,3,3,1],[3,3,3,3],[0,0,0,0],[2,0,2,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,3,3,1],[3,3,3,3],[0,0,0,0],[2,0,2,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2052] [3461, 3462, 4268] :=
    ⟨Fin 4, «FinitePoly [[3,3,3,1],[3,3,3,3],[0,0,0,0],[2,0,2,0]]», Finite.of_fintype _, by decideFin!⟩
