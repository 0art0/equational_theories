
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,0,3,1],[3,2,3,1],[2,2,3,1],[3,2,3,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,0,3,1],[3,2,3,1],[2,2,3,1],[3,2,3,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,0,3,1],[3,2,3,1],[2,2,3,1],[3,2,3,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,0,3,1],[3,2,3,1],[2,2,3,1],[3,2,3,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [635] [55, 639, 642, 835, 845, 1426] :=
    ⟨Fin 4, «FinitePoly [[3,0,3,1],[3,2,3,1],[2,2,3,1],[3,2,3,1]]», by decideFin!⟩
