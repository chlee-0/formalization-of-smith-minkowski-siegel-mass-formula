import SMSFormula.AdelicGaussianResidueRestrictedReplacement
import SMSFormula.RationalAdeleSingularSeriesLocalDensity

/-!
# The Riesz mass of the integral carrier is the real density times the singular series

The integral part `X_a ∩ {x_f integral}` of the value fiber is the carried set of the full
residue set, so its Riesz mass is the value density of the orbit test with `R = univ`
(Riesz evaluation).  That test is a product test whose finite factor is the integral
indicator, so the local product and the block-free Siegel series give, at an adele `a`
with rational-integer finite part `M ≠ 0` and lattice rank at least five,

`σ(X_a ∩ {x_f integral}) = ofReal(Re d_∞(Φ_∞)(a_∞) · ∏'_p δ_p(M))`.

The real factor is the real local density of the normalized Gaussian and is not evaluated;
the local densities `δ_p(M)` are the limits of normalized residue counts.  Nothing is chosen.
-/

noncomputable section

open PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix MeasureTheory
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

variable {n : ℕ}

/-- The value density of the integral orbit test is the real density times the singular series. -/
theorem realValueDensity_gaussianResidueRestrictedUnit_univ_eq_tprod
    (L : PositiveDefiniteIntegralLattice (n + 1)) (hn : 4 ≤ n) (b : ℝ) (a : RationalAdele) {M : ℤ} (hM : M ≠ 0)
    (ha : a.2 = algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ)) (N₀ : ℕ) [NeZero N₀] :
    L.rationalQuadraticSpaceMatrix.realValueDensity
        (gaussianResidueRestrictedUnit L b a N₀ Set.univ).val a =
      (L.rationalQuadraticSpaceMatrix.realLocalValueDensity (gaussianOrbitTestRealFactor L b a)
          (rationalAdeleRealScalar a)).re *
        ∏' p : Nat.Primes, L.localResidueDensity M p := by
  change (L.rationalQuadraticSpaceMatrix.complexValueFourierDensity _ a).re = _
  rw [complexValueFourierDensity_gaussianResidueRestrictedUnit, ha, residueRestrictedIndicator_univ,
    (L.finiteLocalValueDensity_integralIndicator_eq_tprod_localResidueDensity_of_ne_zero hn hM).2,
    Complex.re_mul_ofReal]

/-- The Riesz mass of the integral carrier:
`σ(X_a ∩ {x_f integral}) = ofReal(Re d_∞(Φ_∞)(a_∞) · ∏'_p δ_p(M))`. -/
theorem gaussianFiberMeasure_fiberDividedCarrier_one_eq_tprod
    (L : PositiveDefiniteIntegralLattice (n + 1)) (hn : 4 ≤ n) {b : ℝ} (hb : 0 < b) (a : RationalAdele) {M : ℤ}
    (hM : M ≠ 0) (ha : a.2 = algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ)) :
    gaussianFiberMeasure L (by omega) hb a (fiberDividedCarrier L a 1) =
      ENNReal.ofReal ((L.rationalQuadraticSpaceMatrix.realLocalValueDensity
          (gaussianOrbitTestRealFactor L b a) (rationalAdeleRealScalar a)).re *
        ∏' p : Nat.Primes, L.localResidueDensity M p) := by
  rw [← fiberResidueRestrictedSet_univ L a 1, gaussianFiberMeasure_fiberResidueRestrictedSet,
    realValueDensity_gaussianResidueRestrictedUnit_univ_eq_tprod L hn b a hM ha 1]

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
