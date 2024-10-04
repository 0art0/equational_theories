import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,4,0,5,6,3,7],[7,3,5,6,4,0,2,1],[2,1,6,5,0,4,7,3],[6,4,2,7,3,1,5,0],[0,5,3,1,2,7,4,6],[3,7,0,4,6,5,1,2],[4,6,1,3,7,2,0,5],[5,0,7,2,1,3,6,4]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,2,4,0,5,6,3,7],[7,3,5,6,4,0,2,1],[2,1,6,5,0,4,7,3],[6,4,2,7,3,1,5,0],[0,5,3,1,2,7,4,6],[3,7,0,4,6,5,1,2],[4,6,1,3,7,2,0,5],[5,0,7,2,1,3,6,4]]» : Magma (Fin 8) where
  op := memoFinOp fun x y => [[1,2,4,0,5,6,3,7],[7,3,5,6,4,0,2,1],[2,1,6,5,0,4,7,3],[6,4,2,7,3,1,5,0],[0,5,3,1,2,7,4,6],[3,7,0,4,6,5,1,2],[4,6,1,3,7,2,0,5],[5,0,7,2,1,3,6,4]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,2,4,0,5,6,3,7],[7,3,5,6,4,0,2,1],[2,1,6,5,0,4,7,3],[6,4,2,7,3,1,5,0],[0,5,3,1,2,7,4,6],[3,7,0,4,6,5,1,2],[4,6,1,3,7,2,0,5],[5,0,7,2,1,3,6,4]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [870,883,898,2101,2116,2304,2316] [8,11,14,16,23,26,29,31,40,43,411,414,417,419,427,429,436,440,444,452,455,464,466,473,477,481,489,492,500,504,508,511,513,522,528,543,546,556,562,572,575,614,617,620,622,630,632,639,643,647,655,658,667,669,676,680,684,692,695,703,707,711,714,716,725,731,746,749,759,765,775,778,820,823,833,835,842,846,850,858,861,872,879,887,895,906,910,914,917,919,928,934,949,952,962,968,978,981,1020,1023,1026,1028,1036,1038,1045,1049,1053,1061,1064,1073,1075,1082,1086,1090,1098,1101,1109,1113,1117,1120,1122,1131,1137,1152,1155,1165,1171,1181,1184,1223,1226,1229,1231,1239,1241,1248,1252,1256,1264,1267,1276,1278,1285,1289,1293,1301,1304,1312,1316,1320,1323,1325,1334,1340,1355,1358,1368,1374,1384,1387,1426,1429,1432,1434,1442,1444,1451,1455,1459,1467,1470,1479,1481,1488,1492,1496,1504,1507,1515,1519,1523,1526,1528,1537,1543,1558,1561,1571,1577,1587,1590,1629,1632,1635,1637,1645,1647,1654,1658,1662,1670,1673,1682,1684,1691,1695,1699,1707,1710,1718,1722,1726,1729,1731,1740,1746,1761,1764,1774,1780,1790,1793,1832,1835,1838,1840,1848,1850,1857,1861,1865,1873,1876,1885,1887,1894,1898,1902,1910,1913,1921,1925,1929,1932,1934,1943,1949,1964,1967,1977,1983,1993,1996,2038,2041,2051,2053,2060,2064,2068,2076,2079,2090,2097,2105,2113,2124,2128,2132,2135,2137,2146,2152,2167,2170,2180,2186,2196,2199,2241,2246,2254,2256,2263,2267,2271,2279,2282,2291,2300,2308,2319,2327,2331,2335,2338,2340,2349,2355,2370,2373,2383,2389,2399,2402,2441,2444,2447,2449,2457,2459,2466,2470,2474,2482,2485,2494,2496,2503,2507,2511,2519,2522,2530,2534,2538,2541,2543,2552,2558,2573,2576,2586,2592,2602,2605,2644,2647,2650,2652,2660,2662,2669,2673,2677,2685,2688,2697,2699,2706,2710,2714,2722,2725,2733,2737,2741,2744,2746,2755,2761,2776,2779,2789,2795,2805,2808,2847,2850,2853,2855,2863,2865,2872,2876,2880,2888,2891,2900,2902,2909,2913,2917,2925,2928,2936,2940,2944,2947,2949,2958,2964,2979,2982,2992,2998,3008,3011,3050,3053,3056,3058,3066,3068,3075,3079,3083,3091,3094,3103,3105,3112,3116,3120,3128,3131,3139,3143,3147,3150,3152,3161,3167,3182,3185,3195,3201,3211,3214,3253,3256,3259,3261,3269,3271,3278,3282,3286,3294,3297,3306,3308,3315,3319,3323,3331,3334,3342,3346,3350,3353,3355,3364,3370,3385,3388,3398,3404,3414,3417,3456,3459,3462,3464,3472,3474,3481,3485,3489,3497,3500,3509,3511,3518,3522,3526,3534,3537,3545,3549,3553,3556,3558,3567,3573,3588,3591,3601,3607,3617,3620,3659,3662,3665,3667,3675,3677,3684,3688,3692,3700,3703,3712,3714,3721,3725,3729,3737,3740,3748,3752,3756,3759,3761,3770,3776,3791,3794,3804,3810,3820,3823,3862,3865,3868,3870,3878,3880,3887,3891,3895,3903,3906,3915,3917,3924,3928,3932,3940,3943,3951,3955,3959,3962,3964,3973,3979,3994,3997,4007,4013,4023,4026,4065,4068,4071,4073,4081,4083,4090,4094,4098,4106,4109,4118,4120,4127,4131,4135,4143,4146,4154,4158,4162,4165,4167,4176,4182,4197,4200,4210,4216,4226,4229,4270,4273,4275,4283,4290,4297,4305,4307,4320,4325,4332,4341,4358,4362,4364,4369,4380,4383,4386,4388,4396,4398,4405,4409,4413,4421,4424,4433,4435,4442,4446,4450,4458,4461,4469,4473,4477,4480,4482,4491,4497,4512,4515,4525,4531,4541,4544,4585,4588,4590,4598,4605,4612,4620,4622,4635,4640,4647,4656,4673,4677,4679,4684] :=
    ⟨Fin 8, «FinitePoly [[1,2,4,0,5,6,3,7],[7,3,5,6,4,0,2,1],[2,1,6,5,0,4,7,3],[6,4,2,7,3,1,5,0],[0,5,3,1,2,7,4,6],[3,7,0,4,6,5,1,2],[4,6,1,3,7,2,0,5],[5,0,7,2,1,3,6,4]]», by decideFin!⟩