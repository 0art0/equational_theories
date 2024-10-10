
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,1],[2,1,1],[2,0,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,1],[2,1,1],[2,0,2]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,0,1],[2,1,1],[2,0,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,1],[2,1,1],[2,0,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [429, 829, 1039, 1232, 1481, 2051, 2098, 3519, 4473] [55, 56, 66, 73, 75, 105, 107, 108, 118, 127, 159, 160, 167, 206, 209, 211, 221, 229, 231, 261, 263, 264, 274, 280, 283, 426, 427, 430, 436, 437, 439, 440, 464, 466, 474, 476, 477, 501, 503, 504, 629, 630, 632, 633, 639, 640, 642, 643, 669, 670, 676, 677, 680, 704, 706, 713, 716, 822, 827, 832, 833, 835, 836, 842, 843, 845, 846, 873, 882, 883, 907, 917, 1025, 1028, 1035, 1036, 1038, 1045, 1046, 1048, 1049, 1075, 1076, 1082, 1083, 1086, 1110, 1112, 1119, 1122, 1225, 1228, 1229, 1231, 1238, 1239, 1241, 1242, 1248, 1249, 1251, 1252, 1276, 1279, 1285, 1286, 1288, 1312, 1313, 1315, 1325, 1431, 1432, 1434, 1435, 1441, 1442, 1444, 1445, 1451, 1454, 1455, 1478, 1479, 1482, 1488, 1515, 1519, 1525, 1526, 1631, 1634, 1635, 1637, 1638, 1644, 1645, 1648, 1654, 1655, 1657, 1658, 1681, 1682, 1684, 1691, 1694, 1719, 1722, 1731, 1834, 1840, 1841, 1847, 1848, 1850, 1851, 1857, 1858, 1860, 1861, 1884, 1885, 1887, 1888, 1894, 1921, 1925, 1931, 2037, 2038, 2040, 2041, 2043, 2044, 2050, 2053, 2054, 2060, 2061, 2063, 2064, 2087, 2088, 2090, 2091, 2097, 2101, 2124, 2125, 2127, 2128, 2134, 2241, 2244, 2247, 2253, 2254, 2256, 2257, 2263, 2264, 2266, 2290, 2291, 2294, 2301, 2303, 2327, 2328, 2330, 2337, 2340, 2444, 2446, 2447, 2450, 2456, 2457, 2459, 2460, 2466, 2467, 2469, 2493, 2496, 2497, 2504, 2506, 2531, 2533, 2540, 2541, 2543, 2647, 2649, 2650, 2652, 2659, 2660, 2662, 2669, 2670, 2672, 2696, 2699, 2700, 2706, 2709, 2710, 2733, 2734, 2736, 2743, 2744, 2746, 2849, 2853, 2855, 2856, 2862, 2863, 2865, 2866, 2872, 2873, 2875, 2899, 2902, 2903, 2909, 2910, 2912, 2936, 2937, 2939, 2946, 2947, 2949, 3052, 3055, 3056, 3058, 3065, 3066, 3068, 3069, 3075, 3076, 3078, 3079, 3102, 3103, 3106, 3112, 3113, 3115, 3139, 3142, 3143, 3149, 3150, 3152, 3258, 3259, 3261, 3262, 3268, 3269, 3271, 3272, 3278, 3279, 3281, 3306, 3308, 3309, 3315, 3316, 3342, 3343, 3345, 3346, 3352, 3353, 3458, 3461, 3462, 3464, 3465, 3472, 3474, 3475, 3481, 3482, 3484, 3509, 3512, 3518, 3521, 3545, 3546, 3548, 3549, 3555, 3556, 3558, 3661, 3662, 3664, 3665, 3667, 3668, 3674, 3675, 3677, 3678, 3684, 3685, 3687, 3712, 3714, 3721, 3724, 3748, 3749, 3752, 3759, 3761, 3865, 3867, 3868, 3870, 3871, 3877, 3878, 3880, 3881, 3887, 3888, 3890, 3917, 3924, 3925, 3927, 3951, 3952, 3954, 3961, 3962, 3964, 4066, 4067, 4068, 4070, 4071, 4073, 4074, 4080, 4081, 4083, 4084, 4090, 4091, 4093, 4120, 4127, 4128, 4130, 4155, 4157, 4158, 4164, 4165, 4167, 4269, 4270, 4272, 4273, 4275, 4276, 4283, 4284, 4290, 4291, 4293, 4314, 4320, 4321, 4343, 4396, 4398, 4399, 4405, 4406, 4408, 4433, 4435, 4436, 4442, 4443, 4445, 4472, 4479, 4480, 4482, 4583, 4584, 4585, 4587, 4588, 4590, 4591, 4598, 4605, 4606, 4608, 4629, 4635, 4658] :=
    ⟨Fin 3, «FinitePoly [[0,0,1],[2,1,1],[2,0,2]]», by decideFin!⟩
