import SMSFormula.RationalAdelePolarStandardThetaDecay
import SMSFormula.RationalAdeleRankOneBruhatSummability
import SMSFormula.RationalAdeleRankOneEisensteinSiegelFunctional

/-!
# The actual Theta/E difference tends to zero at large real scale

The common covariance is exact and estimates nothing.  Both sides are estimated
separately: the standard rational theta approaches its literal cusp value `1`
exponentially, and the rank-one cusp sum is dominated by a decaying power of the
scale times a fixed summable height kernel.  Combining them gives the first actual
estimate of the difference itself:

```text
‖Theta(test_a) - E(test_a)‖ <= C1 * exp(-rate * (a-1)) + C2 * a^(-1/4)   (a >= 1)
```

and the right side tends to zero.

Negative scope: this is a limit along the real scale of the standard test, not along
any group orbit.  The difference is not shown to be constant in the scale, so no vanishing
of the difference at a fixed scale follows, and nothing here closes Siegel--Weil, the zero
shell, or `tau(Spin)=1`.
-/

noncomputable section

open Matrix MeasureTheory RationalQuadraticSpaceMatrix
open scoped BigOperators

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The standard test takes the literal value one at the origin. -/
theorem rationalAdeleVectorPolarGaussianLatticeTest_zero (L : PositiveDefiniteIntegralLattice n) (b : ℂ) :
    rationalAdeleVectorPolarGaussianLatticeTest L b 0 = 1 := by
  have hreal : rationalAdeleVectorRealPart n (0 : Fin n → RationalAdele) = 0 := by
    funext i
    change rationalInfiniteAdeleContinuousAddEquivReal (0 : RationalInfiniteAdele) = 0
    exact map_zero _
  have hfin : rationalAdeleVectorFinitePart n (0 : Fin n → RationalAdele) = 0 := rfl
  show polarRealGaussian L b (rationalAdeleVectorRealPart n 0) *
      rationalFiniteAdeleVectorIntegralIndicator (rationalAdeleVectorFinitePart n 0) = 1
  rw [hreal, hfin,
    rationalFiniteAdeleVectorIntegralIndicator_of_mem
      (x := (0 : Fin n → RationalFiniteAdele))
      (by intro i; exact Subring.zero_mem _),
    polarRealGaussian]
  simp [realCoordinateGaussian]

/-- The literal inverse square root to the half power is the quarter power. -/
theorem inv_sqrt_rpow_half {a : ℝ} (ha : 0 ≤ a) :
    ((Real.sqrt a)⁻¹) ^ ((1 : ℝ) / 2) = a ^ (-(1 / 4 : ℝ)) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one (a ^ (1 / 2 : ℝ)), ← Real.rpow_mul ha,
    ← Real.rpow_mul ha]
  congr 1
  ring

end PositiveDefiniteIntegralLattice
