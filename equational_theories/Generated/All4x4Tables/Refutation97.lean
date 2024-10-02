
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0, 2, 2, 3], [3, 0, 3, 0], [0, 1, 2, 3], [0, 2, 2, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0, 2, 2, 3], [3, 0, 3, 0], [0, 1, 2, 3], [0, 2, 2, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0, 2, 2, 3], [3, 0, 3, 0], [0, 1, 2, 3], [0, 2, 2, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0, 2, 2, 3], [3, 0, 3, 0], [0, 1, 2, 3], [0, 2, 2, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [260, 2919, 3306, 3684, 3712] [2, 3, 8, 23, 38, 39, 40, 43, 47, 99, 151, 203, 256, 257, 258, 261, 263, 264, 270, 271, 273, 274, 280, 281, 283, 307, 359, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2848, 2849, 2850, 2853, 2855, 2856, 2863, 2865, 2866, 2873, 2875, 2876, 2900, 2902, 2903, 2910, 2912, 2913, 2936, 2937, 2939, 2940, 2946, 2947, 2949, 3050, 3254, 3255, 3256, 3258, 3259, 3261, 3262, 3268, 3269, 3271, 3272, 3278, 3279, 3281, 3308, 3309, 3315, 3316, 3318, 3319, 3342, 3343, 3345, 3346, 3352, 3353, 3355, 3456, 3660, 3661, 3662, 3664, 3665, 3667, 3668, 3674, 3675, 3677, 3678, 3685, 3687, 3714, 3721, 3722, 3724, 3725, 3748, 3749, 3751, 3752, 3759, 3761, 3862, 4065, 4268, 4269, 4270, 4272, 4273, 4275, 4276, 4283, 4284, 4290, 4291, 4293, 4314, 4320, 4321, 4343, 4380, 4583, 4584, 4585, 4587, 4588, 4590, 4591, 4598, 4599, 4605, 4606, 4608, 4629, 4635, 4636, 4658] :=
    ⟨Fin 4, «FinitePoly [[0, 2, 2, 3], [3, 0, 3, 0], [0, 1, 2, 3], [0, 2, 2, 3]]», by decideFin!⟩