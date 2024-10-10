
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1],[1,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1],[1,0]]» : Magma (Fin 2) where
  op := memoFinOp fun x y => [[0,1],[1,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1],[1,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2113] [47, 99, 151, 203, 255, 307, 359, 413, 416, 420, 426, 430, 437, 467, 474, 476, 501, 503, 619, 623, 629, 633, 640, 642, 670, 677, 679, 704, 706, 819, 826, 832, 836, 843, 845, 873, 882, 907, 1025, 1029, 1035, 1039, 1046, 1048, 1076, 1083, 1085, 1110, 1112, 1238, 1242, 1249, 1251, 1279, 1286, 1288, 1315, 1322, 1427, 1428, 1431, 1435, 1441, 1445, 1454, 1478, 1482, 1516, 1525, 1630, 1631, 1634, 1638, 1644, 1648, 1655, 1657, 1681, 1685, 1692, 1694, 1719, 1721, 1728, 1833, 1834, 1837, 1841, 1847, 1851, 1858, 1860, 1884, 1888, 1895, 1897, 1922, 1924, 1931, 2036, 2037, 2040, 2044, 2050, 2063, 2087, 2091, 2125, 2127, 2134, 2240, 2247, 2257, 2264, 2266, 2301, 2303, 2328, 2330, 2443, 2446, 2460, 2467, 2469, 2497, 2504, 2506, 2531, 2533, 2540, 2646, 2659, 2670, 2672, 2700, 2709, 2734, 2736, 2743, 2849, 2852, 2866, 2873, 2875, 2903, 2910, 2912, 2937, 2939, 2946, 3052, 3055, 3065, 3069, 3076, 3106, 3113, 3115, 3140, 3142, 3149, 3255, 3258, 3262, 3268, 3272, 3279, 3281, 3309, 3316, 3318, 3343, 3345, 3352, 3457, 3458, 3461, 3465, 3475, 3482, 3484, 3512, 3519, 3521, 3546, 3548, 3555, 3660, 3661, 3664, 3668, 3674, 3678, 3685, 3687, 3722, 3724, 3749, 3864, 3867, 3871, 3877, 3881, 3888, 3890, 3918, 3925, 3927, 3952, 3954, 3961, 4066, 4067, 4070, 4074, 4084, 4091, 4093, 4121, 4128, 4130, 4155, 4157, 4164, 4268, 4269, 4272, 4276, 4284, 4291, 4293, 4314, 4321, 4343, 4399, 4406, 4408, 4436, 4443, 4445, 4470, 4472, 4479, 4583, 4584, 4587, 4591, 4599, 4606, 4608, 4629, 4636, 4658] :=
    ⟨Fin 2, «FinitePoly [[0,1],[1,0]]», by decideFin!⟩
