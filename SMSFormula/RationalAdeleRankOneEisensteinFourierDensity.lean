import SMSFormula.RationalAdeleAdditiveQuotient
import Mathlib.MeasureTheory.Group.FundamentalDomain
import SMSFormula.RationalAdeleRankOneAdelicBruhatIntegrable
import SMSFormula.ValueDensityPositiveFunctional

/-!
# The nonzero Fourier coefficients of the Eisenstein--Siegel functional are value densities

The unfolding expresses the frequency-`b` Fourier coefficient of the rank-one
Eisenstein--Siegel functional `E` on `𝔸/ℚ` as the adelic integral
`∫_𝔸 ψ_{-b}(u) B(Φ,u) du` of the adelic Bruhat coefficient.  The complex value density is
by definition the Fourier transform `d_Φ(w) = ∫_𝔸 ψ(-(u w)) B(Φ,u) du`.  Since
`ψ_{-b}(u) = ψ((-b) u) = ψ(-(u b))`, the two agree at `w = b`: the coefficient of `E` at every
nonzero rational frequency is `d_Φ(b)`, with coefficient one.  So in the aggregate comparison the
`E` shell weights are literally one against `d_Φ`; the whole normalization question sits on the
theta side (`τ_W/τ_V`, the horizontal ratio and the Riesz ratio `σ/M_native`).  Nothing is chosen.
-/

noncomputable section

open MeasureTheory PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- The scaled-character integral of the Bruhat coefficient is the value density at the rational
frequency. -/
theorem integral_scaledFourierChar_mul_bruhat_eq_complexValueFourierDensity
    (V : RationalQuadraticSpaceMatrix n) (Phi : (Fin n → RationalAdele) → ℂ) (b : ℚ) :
    ∫ u : RationalAdele, (rationalAdeleScaledFourierChar (-b) u : ℂ) *
        V.rationalAdeleRankOneAdelicBruhatCoefficient Phi u ∂rationalAdeleAddHaarMeasure =
      V.complexValueFourierDensity Phi (algebraMap ℚ RationalAdele b) := by
  rw [complexValueFourierDensity, Fourier.fourierIntegral_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u ↦ ?_)
  simp only [rationalAdeleScaledFourierChar_apply, Circle.smul_def, smul_eq_mul, map_neg, neg_mul,
    mul_comm u]

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

variable {rank : ℕ}

end PositiveDefiniteIntegralLattice
