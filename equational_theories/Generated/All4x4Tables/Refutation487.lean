
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,3,4,5,6,7,1],[4,1,6,0,7,3,5,2],[5,3,2,7,0,1,4,6],[6,7,4,3,1,0,2,5],[7,6,1,5,4,2,0,3],[1,4,7,2,6,5,3,0],[2,0,5,1,3,7,6,4],[3,5,0,6,2,4,1,7]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,2,3,4,5,6,7,1],[4,1,6,0,7,3,5,2],[5,3,2,7,0,1,4,6],[6,7,4,3,1,0,2,5],[7,6,1,5,4,2,0,3],[1,4,7,2,6,5,3,0],[2,0,5,1,3,7,6,4],[3,5,0,6,2,4,1,7]]» : Magma (Fin 8) where
  op := memoFinOp fun x y => [[0,2,3,4,5,6,7,1],[4,1,6,0,7,3,5,2],[5,3,2,7,0,1,4,6],[6,7,4,3,1,0,2,5],[7,6,1,5,4,2,0,3],[1,4,7,2,6,5,3,0],[2,0,5,1,3,7,6,4],[3,5,0,6,2,4,1,7]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,2,3,4,5,6,7,1],[4,1,6,0,7,3,5,2],[5,3,2,7,0,1,4,6],[6,7,4,3,1,0,2,5],[7,6,1,5,4,2,0,3],[1,4,7,2,6,5,3,0],[2,0,5,1,3,7,6,4],[3,5,0,6,2,4,1,7]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [63, 503, 706, 1312, 1692, 2447, 2853, 3076] [439, 466, 473, 476, 513, 619, 716, 832, 882, 1028, 1038, 1045, 1075, 1082, 1109, 1122, 1231, 1241, 1248, 1278, 1285, 1454, 1478, 1637, 1654, 1684, 1691, 1731, 1840, 1857, 1887, 1894, 1921, 2053, 2060, 2097, 2124, 2137, 2863, 3069, 3078, 3079, 3254, 3255, 3256, 3261, 3271, 3278, 3306, 3308, 3315, 3316, 3318, 3346, 3353, 3457, 3458, 3459, 3511, 3518, 3519, 3521, 3867, 3870, 3877, 3880, 3887, 3925, 3928, 3952, 3955, 3962, 4070, 4073, 4080, 4083, 4090, 4128, 4131, 4155, 4158, 4165, 4268, 4275, 4283, 4314, 4320, 4598, 4606, 4635, 4666] :=
    ⟨Fin 8, «FinitePoly [[0,2,3,4,5,6,7,1],[4,1,6,0,7,3,5,2],[5,3,2,7,0,1,4,6],[6,7,4,3,1,0,2,5],[7,6,1,5,4,2,0,3],[1,4,7,2,6,5,3,0],[2,0,5,1,3,7,6,4],[3,5,0,6,2,4,1,7]]», by decideFin!⟩
