import SMSFormula.RationalAdeleRankOneAdelicEisensteinSiegelBounded

/-!
# Continuity and integrability of the adelic rank-one cusp functional

An arbitrary adelic Bruhat coefficient is a parameterized integral of the
quadratic phase against the fixed test function.  Dominated convergence makes
this coefficient continuous whenever the test is integrable.

For the concrete polar Gaussian--lattice test, the rational-height majorant is
uniform on the standard additive block.  The Weierstrass test therefore makes
the convergent cusp sum continuous on that block.  Its continuous surjection
onto `RationalAdele / ℚ` is a quotient map because the block is compact and the
target is Hausdorff.  Thus the already defined quotient lift is continuous,
without selecting a representative.  The preceding uniform bound then gives
integrability against the canonical Haar probability.

No quotient section, shell scaling, theta comparison, generic Eisenstein
series, or new measure normalization is introduced.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- The zero-frequency adelic Bruhat coefficient varies continuously with its
unipotent parameter for every integrable test. -/
theorem continuous_rationalAdeleRankOneAdelicBruhatCoefficient
    (V : RationalQuadraticSpaceMatrix n)
    (Phi : (Fin n → RationalAdele) → ℂ)
    (hPhi : Integrable Phi (rationalAdeleCoordinateAddHaarMeasure n)) :
    Continuous (fun u : RationalAdele =>
      V.rationalAdeleRankOneAdelicBruhatCoefficient Phi u) := by
  have heq : (fun u : RationalAdele =>
      V.rationalAdeleRankOneAdelicBruhatCoefficient Phi u) =
      fun u => ∫ x : Fin n → RationalAdele,
        (V.rationalAdeleRankOneQuadraticPhase u x : ℂ) * Phi x
          ∂rationalAdeleCoordinateAddHaarMeasure n := by
    funext u
    unfold rationalAdeleRankOneAdelicBruhatCoefficient rationalAdeleRankOneWeylOperator
      rationalAdeleRankOneUnipotentOperator Fourier.fourierIntegral
      VectorFourier.fourierIntegral
    simp
  rw [heq, continuous_iff_continuousAt]
  intro u
  refine tendsto_integral_filter_of_dominated_convergence
    (fun x => ‖Phi x‖) ?_ ?_ hPhi.norm ?_
  · exact Filter.Eventually.of_forall fun v =>
      (V.integrable_rationalAdeleRankOneUnipotentOperator v Phi hPhi).aestronglyMeasurable
  · filter_upwards
    intro v
    filter_upwards
    intro x
    rw [norm_mul, Circle.norm_coe, one_mul]
  · filter_upwards
    intro x
    exact
      (((V.continuous_rationalAdeleRankOneQuadraticPhase.comp
          (continuous_id.prodMk continuous_const)).subtype_val.mul
            continuous_const).tendsto u)

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

open RationalQuadraticSpaceMatrix

variable {n : ℕ}

end PositiveDefiniteIntegralLattice

end
