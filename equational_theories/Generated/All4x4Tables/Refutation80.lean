
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,0,1],[1,1,1,0],[3,3,2,2],[2,2,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,0,1],[1,1,1,0],[3,3,2,2],[2,2,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,0,0,1],[1,1,1,0],[3,3,2,2],[2,2,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,0,1],[1,1,1,0],[3,3,2,2],[2,2,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [160, 377, 1237, 2054, 2653, 2666, 2873, 3723, 4403, 4472] [55, 56, 105, 107, 108, 159, 206, 209, 211, 264, 378, 426, 427, 429, 430, 436, 437, 439, 440, 629, 630, 632, 633, 639, 640, 642, 643, 832, 833, 835, 836, 842, 843, 845, 846, 1035, 1036, 1038, 1039, 1045, 1046, 1048, 1049, 1238, 1239, 1241, 1242, 1248, 1249, 1251, 1252, 1431, 1432, 1434, 1435, 1441, 1444, 1445, 1451, 1634, 1635, 1637, 1638, 1644, 1645, 1648, 1655, 1657, 1834, 1840, 1841, 1847, 1848, 1851, 1857, 1858, 1860, 2037, 2038, 2040, 2041, 2043, 2050, 2053, 2063, 2064, 2241, 2244, 2247, 2253, 2254, 2256, 2257, 2263, 2266, 2444, 2447, 2450, 2456, 2459, 2460, 2466, 2467, 2469, 2647, 2649, 2650, 2652, 2659, 2662, 2669, 2670, 2849, 2853, 2855, 2862, 2863, 2865, 2866, 2872, 3052, 3055, 3065, 3069, 3076, 3078, 3258, 3259, 3261, 3262, 3268, 3269, 3271, 3272, 3278, 3279, 3281, 3306, 3308, 3309, 3315, 3316, 3342, 3343, 3345, 3346, 3352, 3353, 3461, 3462, 3464, 3465, 3472, 3474, 3475, 3481, 3482, 3484, 3509, 3511, 3512, 3519, 3521, 3545, 3546, 3548, 3549, 3555, 3556, 3558, 3661, 3662, 3664, 3665, 3667, 3674, 3675, 3677, 3678, 3684, 3685, 3687, 3712, 3714, 3724, 3725, 3748, 3749, 3752, 3759, 3761, 3865, 3867, 3868, 3870, 3877, 3878, 3880, 3881, 3887, 3888, 3890, 3917, 3924, 3925, 3928, 3951, 3952, 3954, 3955, 3961, 3962, 3964, 4066, 4067, 4070, 4074, 4080, 4081, 4083, 4084, 4090, 4091, 4093, 4121, 4128, 4130, 4155, 4157, 4158, 4164, 4165, 4167, 4269, 4270, 4272, 4273, 4275, 4276, 4283, 4284, 4290, 4291, 4293, 4314, 4320, 4321, 4343, 4396, 4398, 4405, 4406, 4408, 4433, 4435, 4436, 4442, 4443, 4445, 4473, 4479, 4480, 4482, 4583, 4584, 4587, 4588, 4590, 4591, 4599, 4605, 4606, 4608, 4629, 4635, 4636, 4658] :=
    ⟨Fin 4, «FinitePoly [[0,0,0,1],[1,1,1,0],[3,3,2,2],[2,2,3,3]]», by decideFin!⟩
