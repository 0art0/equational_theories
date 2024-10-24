
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,4,0,6,5,3],[4,3,1,5,2,0,6],[0,6,5,1,3,4,2],[5,0,6,2,4,3,1],[3,4,2,6,0,1,5],[2,1,3,4,5,6,0],[6,5,0,3,1,2,4]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,2,4,0,6,5,3],[4,3,1,5,2,0,6],[0,6,5,1,3,4,2],[5,0,6,2,4,3,1],[3,4,2,6,0,1,5],[2,1,3,4,5,6,0],[6,5,0,3,1,2,4]]» : Magma (Fin 7) where
  op := memoFinOp fun x y => [[1,2,4,0,6,5,3],[4,3,1,5,2,0,6],[0,6,5,1,3,4,2],[5,0,6,2,4,3,1],[3,4,2,6,0,1,5],[2,1,3,4,5,6,0],[6,5,0,3,1,2,4]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,2,4,0,6,5,3],[4,3,1,5,2,0,6],[0,6,5,1,3,4,2],[5,0,6,2,4,3,1],[3,4,2,6,0,1,5],[2,1,3,4,5,6,0],[6,5,0,3,1,2,4]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [880] [47, 99, 151, 221, 255, 411, 614, 819, 826, 832, 833, 835, 836, 842, 843, 845, 846, 870, 872, 879, 882, 883, 906, 907, 917, 1020, 1238, 1239, 1242, 1248, 1249, 1251, 1252, 1276, 1278, 1279, 1285, 1286, 1288, 1315, 1322, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3456, 3659, 3862, 4065, 4268, 4269, 4270, 4272, 4273, 4275, 4283, 4284, 4291, 4293, 4321, 4343, 4380, 4583, 4584, 4585, 4587, 4590, 4606, 4608, 4635, 4636, 4658] :=
    ⟨Fin 7, «FinitePoly [[1,2,4,0,6,5,3],[4,3,1,5,2,0,6],[0,6,5,1,3,4,2],[5,0,6,2,4,3,1],[3,4,2,6,0,1,5],[2,1,3,4,5,6,0],[6,5,0,3,1,2,4]]», Finite.of_fintype _, by decideFin!⟩
