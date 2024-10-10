
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following refutation as produced by
random generation of polynomials:
'(1 * x**2 + 2 * y**2 + 0 * x + 0 * y + 2 * x * y) % 4' (0, 306, 307, 324, 325, 326, 358, 360, 374, 377, 380, 3252, 3253, 3254, 3255, 3256, 3314, 3315, 3316, 3317, 3318, 3319, 3320, 3321, 3322, 3323, 3455, 3456, 3457, 3458, 3459, 3517, 3518, 3519, 3520, 3521, 3522, 3523, 3524, 3525, 3526, 3658, 3659, 3663, 3664, 3665, 3713, 3714, 3715, 3723, 3724, 3725, 3734, 3735, 3736, 3737, 3861, 3863, 3866, 3869, 3872, 3914, 3917, 3920, 3924, 3927, 3930, 3934, 3938, 3942, 3946, 4064, 4066, 4069, 4072, 4075, 4117, 4120, 4123, 4127, 4130, 4133, 4137, 4141, 4145, 4149, 4267, 4281, 4313, 4314, 4338, 4356, 4379, 4381, 4394, 4397, 4400, 4432, 4435, 4438, 4469, 4472, 4475, 4506, 4510, 4514, 4518, 4583, 4598, 4601, 4630, 4654, 4674)
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly x² + 2 * y² + 2 * x * y % 4» : Magma (Fin 4) where
  op := memoFinOp fun x y => x*x + 2 * y*y + 2 * x * y

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly x² + 2 * y² + 2 * x * y % 4» :
  ∃ (G : Type) (_ : Magma G), Facts G [327, 381, 3738, 4519] [47, 99, 151, 203, 255, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3258, 3259, 3261, 3262, 3268, 3269, 3271, 3272, 3278, 3279, 3281, 3306, 3308, 3309, 3342, 3343, 3345, 3346, 3352, 3353, 3461, 3462, 3464, 3465, 3472, 3474, 3475, 3481, 3482, 3484, 3509, 3511, 3512, 3545, 3546, 3548, 3549, 3555, 3556, 3558, 3661, 3662, 3667, 3668, 3674, 3675, 3677, 3678, 3684, 3685, 3687, 3712, 3721, 3722, 3748, 3749, 3751, 3752, 3758, 3759, 3761, 3865, 3868, 3871, 3877, 3878, 3880, 3881, 3887, 3888, 3890, 3917, 3924, 3927, 3951, 3952, 3954, 3955, 3961, 3962, 3964, 4066, 4068, 4071, 4074, 4080, 4081, 4083, 4084, 4090, 4091, 4093, 4120, 4127, 4130, 4155, 4157, 4158, 4164, 4165, 4167, 4269, 4270, 4272, 4273, 4275, 4276, 4283, 4284, 4290, 4291, 4293, 4320, 4321, 4343, 4396, 4399, 4405, 4406, 4408, 4435, 4442, 4443, 4445, 4472, 4479, 4480, 4482, 4583, 4585, 4587, 4588, 4590, 4591, 4598, 4605, 4606, 4608, 4629, 4635, 4636, 4658] :=
    ⟨Fin 4, «FinitePoly x² + 2 * y² + 2 * x * y % 4», by decideFin!⟩
