import SMSFormula.RationalCliffordGeneralSpinThetaZeroCalibration

/-!
# Probability normalization of the ordinary all-rational theta integral

The horizontal periodization scalar calibrates the ordinary theta cutoff
integral.  Dividing by the common logarithmic cutoff mass and the canonical
ambient Spin quotient volume defines a section-free nonnegative functional.
The zero-shell calibration makes its zero contribution exactly `Phi 0`, and
nonnegative Tonelli reassembles the remaining represented-norm contributions
without choosing a rational vector or complement witness.

This file does not identify the nonzero contributions with a pointwise
weighted theta function.  Such a comparison involves the ratio between the
ambient horizontal scalar and each locally supplied complement scalar.
-/

noncomputable section

open MeasureTheory RationalQuadraticSpaceMatrix
open scoped ENNReal NNReal

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

/-- The probability-normalized ordinary theta cutoff functional on the
existing rational `GSpin` quotient. -/
noncomputable def probabilityNormalizedFullAdelicCliffordGeneralSpinTheta
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hr : 1 ≤ r)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {cutoffProduct : ℝ} (hcutoffProduct : 0 < cutoffProduct)
    (hconv : massLocalInverseProductTendsTo L cutoffProduct)
    (Phi : (Fin (r + 2) → RationalAdele) → ℝ≥0∞)
    (f : ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  let D := cliffordSpinCandidateRawOnoTamagawaDataOfLattice
    L (by omega) inst hcutoffProduct hconv
  let horizontalScalar :=
    L.periodizedHorizontalRawSOFiberHaarBoundRightHaarScalar
      (by omega) inst hcutoffProduct hconv
  ((horizontalScalar : ℝ≥0∞) *
      L.fullAdelicCliffordGeneralSpinThetaLogCutoffIntegral Phi f) /
    (rationalIdeleClassLogCutoffLIntegral f *
      D.spinTamagawaNumberENNReal)

/-- The contribution of one represented nonzero rational norm to the
probability-normalized ordinary quotient theta functional. -/
noncomputable def probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hr : 1 ≤ r)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {cutoffProduct : ℝ} (hcutoffProduct : 0 < cutoffProduct)
    (hconv : massLocalInverseProductTendsTo L cutoffProduct)
    (a : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm)
    (Phi : (Fin (r + 2) → RationalAdele) → ℝ≥0∞)
    (f : ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  let D := cliffordSpinCandidateRawOnoTamagawaDataOfLattice
    L (by omega) inst hcutoffProduct hconv
  let horizontalScalar :=
    L.periodizedHorizontalRawSOFiberHaarBoundRightHaarScalar
      (by omega) inst hcutoffProduct hconv
  ((horizontalScalar : ℝ≥0∞) *
      L.fullAdelicCliffordGeneralSpinRepresentedNormThetaLogCutoffIntegral
        a Phi f) /
    (rationalIdeleClassLogCutoffLIntegral f *
      D.spinTamagawaNumberENNReal)

/-- Exact section-free zero/nonzero expansion of the probability-normalized
ordinary quotient theta functional. -/
theorem probabilityNormalizedFullAdelicCliffordGeneralSpinTheta_eq_zero_add_representedNorm
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hr : 1 ≤ r)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {cutoffProduct : ℝ} (hcutoffProduct : 0 < cutoffProduct)
    (hconv : massLocalInverseProductTendsTo L cutoffProduct)
    (Phi : (Fin (r + 2) → RationalAdele) → ℝ≥0∞)
    (hPhi : Measurable Phi)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f)
    (hcutoffMass_ne_zero : rationalIdeleClassLogCutoffLIntegral f ≠ 0)
    (hcutoffMass_ne_top : rationalIdeleClassLogCutoffLIntegral f ≠ ⊤) :
    L.probabilityNormalizedFullAdelicCliffordGeneralSpinTheta
        hr inst hcutoffProduct hconv Phi f =
      Phi 0 +
        ∑' a : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm,
          L.probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta
            hr inst hcutoffProduct hconv a Phi f := by
  let V := L.rationalQuadraticSpaceMatrix
  let D := cliffordSpinCandidateRawOnoTamagawaDataOfLattice
    L (by omega : 3 ≤ r + 2) inst hcutoffProduct hconv
  let horizontalScalar :=
    L.periodizedHorizontalRawSOFiberHaarBoundRightHaarScalar
      (by omega : 3 ≤ r + 2) inst hcutoffProduct hconv
  let cutoffMass := rationalIdeleClassLogCutoffLIntegral f
  let spinVolume := D.spinTamagawaNumberENNReal
  let denominator := cutoffMass * spinVolume
  let zeroIntegral : ℝ≥0∞ :=
    ∫⁻ Z,
      f (V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule Z)
    ∂(V.fullAdelicCliffordGeneralSpinHorizontalMeasurableWeilData
      |>.quotientMeasure)
  let totalIntegral :=
    L.fullAdelicCliffordGeneralSpinThetaLogCutoffIntegral Phi f
  let fiberIntegral := fun a : V.RepresentedNonzeroRationalNorm ↦
    L.fullAdelicCliffordGeneralSpinRepresentedNormThetaLogCutoffIntegral
      a Phi f
  have hrelative : D.IsOnoRelativeTamagawaComparison := by
    simpa only [D] using
      L.cliffordSpinCandidateRawOnoTamagawaDataOfLattice_isOnoRelativeComparison
        (by omega) inst hcutoffProduct hconv
  have hspinVolume_ne_zero : spinVolume ≠ 0 :=
    D.spinTamagawaNumberENNReal_ne_zero
  have hspinVolume_ne_top : spinVolume ≠ ⊤ :=
    D.spinTamagawaNumberENNReal_ne_top_of_onoRelativeComparison hrelative
  have hdenominator_ne_zero : denominator ≠ 0 :=
    mul_ne_zero hcutoffMass_ne_zero hspinVolume_ne_zero
  have hdenominator_ne_top : denominator ≠ ⊤ :=
    ENNReal.mul_ne_top hcutoffMass_ne_top hspinVolume_ne_top
  have hdecomposition :
      totalIntegral = Phi 0 * zeroIntegral +
        ∑' a : V.RepresentedNonzeroRationalNorm, fiberIntegral a := by
    simpa only [V, totalIntegral, zeroIntegral, fiberIntegral] using
      L.fullAdelicCliffordGeneralSpinThetaLogCutoffIntegral_eq_zero_add_representedNorm
        Phi hPhi f hf
  have hzero :
      (horizontalScalar : ℝ≥0∞) * zeroIntegral = denominator := by
    simpa only [V, D, horizontalScalar, cutoffMass, spinVolume, denominator,
      zeroIntegral] using
      L.horizontalScalar_mul_lintegral_logCutoff_eq_cutoffMass_mul_spinTamagawa
        hr inst hcutoffProduct hconv f hf
  have hzeroTerm :
      (horizontalScalar : ℝ≥0∞) * (Phi 0 * zeroIntegral) =
        Phi 0 * denominator := by
    calc
      (horizontalScalar : ℝ≥0∞) * (Phi 0 * zeroIntegral) =
          Phi 0 * ((horizontalScalar : ℝ≥0∞) * zeroIntegral) := by ac_rfl
      _ = Phi 0 * denominator := by rw [hzero]
  have htsumDiv :
      (∑' a : V.RepresentedNonzeroRationalNorm,
          (horizontalScalar : ℝ≥0∞) * fiberIntegral a) / denominator =
        ∑' a : V.RepresentedNonzeroRationalNorm,
          ((horizontalScalar : ℝ≥0∞) * fiberIntegral a) / denominator := by
    rw [div_eq_mul_inv, ← ENNReal.tsum_mul_right]
    simp only [div_eq_mul_inv]
  unfold probabilityNormalizedFullAdelicCliffordGeneralSpinTheta
  unfold probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta
  dsimp only
  change
    ((horizontalScalar : ℝ≥0∞) * totalIntegral) / denominator =
      Phi 0 +
        ∑' a : V.RepresentedNonzeroRationalNorm,
          ((horizontalScalar : ℝ≥0∞) * fiberIntegral a) / denominator
  rw [hdecomposition, mul_add, hzeroTerm, ← ENNReal.tsum_mul_left]
  rw [ENNReal.add_div]
  rw [mul_div_assoc, ENNReal.div_self hdenominator_ne_zero
    hdenominator_ne_top, mul_one]
  rw [htsumDiv]

end PositiveDefiniteIntegralLattice

end
