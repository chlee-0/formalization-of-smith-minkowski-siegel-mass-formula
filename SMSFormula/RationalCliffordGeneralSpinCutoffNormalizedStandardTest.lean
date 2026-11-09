import SMSFormula.RationalCliffordGeneralSpinCutoffNormalizedThetaReal
import SMSFormula.RationalCliffordGeneralSpinPolarGaussianLatticeCutoffFinite
import SMSFormula.RationalAdeleThetaEisensteinDifferenceDecay

/-!
# The cutoff-normalized expansion at the standard test: not vacuous

The finiteness layer was conditional on the raw theta cutoff integral of the chosen test being
finite.  For the standard polar Gaussian--lattice test and the existing unit logarithmic cutoff
that hypothesis is already proved, so the whole layer instantiates unconditionally there.

The standard test takes the value one at the origin, so its zero-orbit coefficient is the
intrinsic Spin quantity itself:

```text
I_V(Phi_a) = t_V + sum_a R_a(Phi_a),
I_V(Phi_a).toReal = t_V.toReal + (sum_a R_a(Phi_a)).toReal.
```

Negative scope: an instantiation, not a new estimate.  Nothing evaluates `t_V`, nothing compares
the shell terms with the Eisenstein side, and no covariance or separating pair is supplied.
-/

noncomputable section

open MeasureTheory RationalQuadraticSpaceMatrix
open scoped ENNReal NNReal

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

/-- The standard nonnegative test takes the value one at the origin. -/
@[simp]
theorem rationalAdeleVectorPolarGaussianLatticeTestENNReal_zero
    {n : ℕ} (L : PositiveDefiniteIntegralLattice n) (a : ℝ) :
    rationalAdeleVectorPolarGaussianLatticeTestENNReal L a 0 = 1 := by
  rw [rationalAdeleVectorPolarGaussianLatticeTestENNReal,
    L.rationalAdeleVectorPolarGaussianLatticeTest_zero ((a : ℝ) : ℂ)]
  simp

/-- The cutoff-normalized functional is finite at the standard test. -/
theorem cutoffNormalizedFullAdelicCliffordGeneralSpinTheta_standard_ne_top
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hr : 1 ≤ r)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {cutoffProduct : ℝ} (hcutoffProduct : 0 < cutoffProduct)
    (hconv : massLocalInverseProductTendsTo L cutoffProduct)
    {a : ℝ} (ha : 0 < a) :
    L.cutoffNormalizedFullAdelicCliffordGeneralSpinTheta hr inst hcutoffProduct hconv
        (rationalAdeleVectorPolarGaussianLatticeTestENNReal L a)
        rationalIdeleClassUnitLogCutoff ≠ ⊤ :=
  L.cutoffNormalizedFullAdelicCliffordGeneralSpinTheta_ne_top hr inst hcutoffProduct hconv _ _
    rationalIdeleClassLogCutoffLIntegral_unit_ne_zero
    (L.fullAdelicCliffordGeneralSpinPolarGaussianLatticeThetaLogCutoffIntegral_ne_top
      hr inst hcutoffProduct hconv ha)

/-- The expansion at the standard test: the zero-orbit coefficient is the intrinsic Spin
quantity itself, because the test is one at the origin. -/
theorem cutoffNormalizedFullAdelicCliffordGeneralSpinTheta_standard_eq
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hr : 1 ≤ r)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {cutoffProduct : ℝ} (hcutoffProduct : 0 < cutoffProduct)
    (hconv : massLocalInverseProductTendsTo L cutoffProduct)
    (a : ℝ) :
    L.cutoffNormalizedFullAdelicCliffordGeneralSpinTheta hr inst hcutoffProduct hconv
        (rationalAdeleVectorPolarGaussianLatticeTestENNReal L a)
        rationalIdeleClassUnitLogCutoff =
      (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
          L (by omega) inst hcutoffProduct hconv).spinTamagawaNumberENNReal +
        ∑' b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm,
          L.cutoffNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta
            hr inst hcutoffProduct hconv b
            (rationalAdeleVectorPolarGaussianLatticeTestENNReal L a)
            rationalIdeleClassUnitLogCutoff := by
  rw [L.cutoffNormalizedFullAdelicCliffordGeneralSpinTheta_eq_spinVolume_add_representedNorm
    hr inst hcutoffProduct hconv _
    (L.measurable_rationalAdeleVectorPolarGaussianLatticeTestENNReal a)
    _ measurable_rationalIdeleClassUnitLogCutoff
    rationalIdeleClassLogCutoffLIntegral_unit_ne_zero
    rationalIdeleClassLogCutoffLIntegral_unit_ne_top,
    L.rationalAdeleVectorPolarGaussianLatticeTestENNReal_zero a, mul_one]

/-- The real-valued form at the standard test. -/
theorem toReal_cutoffNormalizedFullAdelicCliffordGeneralSpinTheta_standard
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hr : 1 ≤ r)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {cutoffProduct : ℝ} (hcutoffProduct : 0 < cutoffProduct)
    (hconv : massLocalInverseProductTendsTo L cutoffProduct)
    {a : ℝ} (ha : 0 < a) :
    (L.cutoffNormalizedFullAdelicCliffordGeneralSpinTheta hr inst hcutoffProduct hconv
        (rationalAdeleVectorPolarGaussianLatticeTestENNReal L a)
        rationalIdeleClassUnitLogCutoff).toReal =
      (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
          L (by omega) inst hcutoffProduct hconv).spinTamagawaNumberENNReal.toReal +
        (∑' b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm,
          L.cutoffNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta
            hr inst hcutoffProduct hconv b
            (rationalAdeleVectorPolarGaussianLatticeTestENNReal L a)
            rationalIdeleClassUnitLogCutoff).toReal := by
  rw [L.toReal_cutoffNormalizedFullAdelicCliffordGeneralSpinTheta_eq
    hr inst hcutoffProduct hconv _
    (L.measurable_rationalAdeleVectorPolarGaussianLatticeTestENNReal a)
    _ measurable_rationalIdeleClassUnitLogCutoff
    rationalIdeleClassLogCutoffLIntegral_unit_ne_zero
    rationalIdeleClassLogCutoffLIntegral_unit_ne_top
    (L.fullAdelicCliffordGeneralSpinPolarGaussianLatticeThetaLogCutoffIntegral_ne_top
      hr inst hcutoffProduct hconv ha),
    L.rationalAdeleVectorPolarGaussianLatticeTestENNReal_zero a]
  simp

end PositiveDefiniteIntegralLattice

end
