
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,3,1],[2,1,2,3],[0,1,2,1],[0,1,2,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,3,1],[2,1,2,3],[0,1,2,1],[0,1,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,1,3,1],[2,1,2,3],[0,1,2,1],[0,1,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,3,1],[2,1,2,3],[0,1,2,1],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2381, 2753] [419, 429, 430, 436, 437, 440, 466, 473, 513, 632, 642, 669, 679, 713, 825, 836, 843, 845, 872, 879, 1023, 1036, 1075, 1085, 1112, 1122, 1249, 1278, 1288, 1315, 1434, 1444, 1451, 1491, 1518, 1525, 1657, 1721, 1731, 1840, 1860, 1861, 1897, 2043, 2063, 2100, 2137, 2240, 2243, 2246, 2256, 2266, 2293, 2303, 2330, 2340, 2443, 2449, 2459, 2469, 2496, 2506, 2533, 2543, 2646, 2652, 2662, 2672, 2699, 2709, 2736, 2746, 2849, 2855, 2865, 2875, 2902, 2912, 2939, 2949, 3052, 3058, 3068, 3078, 3105, 3115, 3142, 3152, 3261, 3271, 3278, 3306, 3346, 3353, 3458, 3464, 3474, 3481, 3484, 3509, 3519, 3546, 3549, 3556, 3661, 3664, 3667, 3677, 3687, 3712, 3724, 3725, 3749, 3752, 3759, 3925, 3952, 3962, 4068, 4128, 4165, 4275, 4320, 4382, 4388, 4396, 4399, 4406, 4432, 4435, 4442, 4445, 4473, 4480, 4483, 4606] :=
    ⟨Fin 4, «FinitePoly [[0,1,3,1],[2,1,2,3],[0,1,2,1],[0,1,2,3]]», by decideFin!⟩
