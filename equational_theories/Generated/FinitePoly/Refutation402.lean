
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following refutation as produced by
random generation of polynomials:
'(0 * x**2 + 0 * y**2 + 1 * x + 3 * y + 0 * x * y) % 4' (0, 7, 10, 15, 39, 410, 413, 418, 426, 435, 439, 443, 454, 465, 499, 503, 507, 512, 527, 542, 574, 816, 819, 822, 834, 841, 845, 849, 857, 869, 905, 909, 913, 916, 927, 951, 977, 1019, 1022, 1027, 1035, 1044, 1048, 1052, 1063, 1074, 1108, 1112, 1116, 1121, 1136, 1151, 1183, 1628, 1634, 1636, 1644, 1646, 1657, 1669, 1672, 1690, 1717, 1728, 1730, 1739, 1745, 1773, 1779, 1831, 1834, 1839, 1847, 1856, 1860, 1864, 1875, 1886, 1920, 1924, 1928, 1933, 1948, 1963, 1995, 2440, 2443, 2446, 2458, 2465, 2469, 2473, 2481, 2493, 2529, 2533, 2537, 2540, 2551, 2575, 2601, 3049, 3078, 3102, 3104, 3111, 3138, 3252, 3255, 3260, 3268, 3277, 3281, 3285, 3296, 3305, 3314, 3318, 3322, 3333, 3352, 3397, 3413, 3658, 3661, 3664, 3676, 3683, 3687, 3691, 3699, 3713, 3720, 3724, 3728, 3736, 3760, 3809, 3822, 3861, 3864, 3869, 3877, 3886, 3890, 3894, 3905, 3914, 3923, 3927, 3931, 3942, 3961, 4006, 4022, 4269, 4274, 4289, 4296, 4306, 4340, 4368, 4587, 4589, 4597, 4619, 4621, 4646, 4672)
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly x + 3 * y % 4» : Magma (Fin 4) where
  op := memoFinOp fun x y => x + 3 * y

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly x + 3 * y % 4» :
  ∃ (G : Type) (_ : Magma G), Facts G [11, 455, 508, 543, 914, 928, 952, 978, 1053, 1117, 1137, 1152, 1670, 1673, 1740, 1746, 1774, 1876, 1929, 1964, 1996, 2474, 2482, 2538, 2552, 2576, 2602, 3079, 3103, 3105, 3112, 3139, 3297, 3398, 3737, 3823, 3895, 4007, 4297, 4620] [47, 99, 151, 203, 255, 307, 412, 413, 416, 417, 420, 426, 429, 430, 437, 439, 463, 464, 467, 473, 474, 476, 477, 501, 503, 510, 511, 614, 818, 819, 822, 825, 826, 832, 833, 836, 843, 845, 869, 872, 873, 879, 880, 882, 883, 907, 909, 916, 919, 1021, 1022, 1025, 1026, 1029, 1035, 1038, 1039, 1046, 1048, 1072, 1073, 1076, 1082, 1083, 1085, 1086, 1110, 1112, 1119, 1120, 1223, 1426, 1630, 1631, 1632, 1634, 1638, 1644, 1648, 1654, 1655, 1657, 1681, 1682, 1684, 1685, 1692, 1694, 1695, 1719, 1721, 1722, 1728, 1833, 1834, 1837, 1838, 1841, 1847, 1850, 1851, 1858, 1860, 1884, 1885, 1888, 1894, 1895, 1897, 1898, 1922, 1924, 1931, 1932, 2035, 2238, 2442, 2443, 2446, 2449, 2450, 2456, 2457, 2460, 2467, 2469, 2493, 2496, 2497, 2503, 2504, 2506, 2507, 2531, 2533, 2540, 2543, 2644, 2847, 3051, 3052, 3053, 3055, 3056, 3058, 3059, 3065, 3066, 3068, 3069, 3075, 3076, 3078, 3102, 3106, 3113, 3115, 3116, 3140, 3142, 3143, 3149, 3150, 3152, 3254, 3255, 3258, 3259, 3262, 3268, 3271, 3272, 3279, 3281, 3308, 3309, 3316, 3318, 3342, 3343, 3345, 3346, 3352, 3456, 3660, 3661, 3664, 3667, 3668, 3674, 3675, 3678, 3685, 3687, 3712, 3722, 3724, 3748, 3749, 3751, 3752, 3759, 3864, 3867, 3868, 3871, 3877, 3880, 3881, 3888, 3890, 3917, 3918, 3925, 3927, 3951, 3952, 3954, 3955, 3961, 3964, 4065, 4268, 4269, 4272, 4273, 4276, 4283, 4284, 4291, 4293, 4314, 4320, 4321, 4343, 4380, 4583, 4584, 4585, 4587, 4591, 4599, 4605, 4606, 4608, 4629, 4635, 4636, 4658] :=
    ⟨Fin 4, «FinitePoly x + 3 * y % 4», by decideFin!⟩
