import SMSFormula.RationalQuadraticIsometrySpinCandidateRepresentedNormOneShellCalibration
import SMSFormula.RationalCliffordGeneralSpinRelativeUnitCutoff

/-!
# Calibration of the zero theta shell

For the canonical lattice raw Spin datum, multiplying the bare horizontal
quotient logarithmic-cutoff integral by the existing horizontal periodization
scalar gives exactly the common cutoff mass times the ambient Spin quotient
volume.  The proof compares the quotient integral with the literal raw
horizontal bound, evaluates its identity fiber through the doubled idele
logarithm, and uses the already closed specialized Spin--SO relative theorem.

Every factor remains visible until the exact cancellation of `2⁻¹ * 2`.
No Tamagawa value, new measure, representative, presentation, or chart is
introduced.
-/

noncomputable section

open MeasureTheory RationalQuadraticSpaceMatrix
open scoped ENNReal NNReal

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

/-- Exact zero-shell normalization on the existing horizontal quotient. -/
theorem horizontalScalar_mul_lintegral_logCutoff_eq_cutoffMass_mul_spinTamagawa
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hr : 1 ≤ r)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {cutoffProduct : ℝ} (hcutoffProduct : 0 < cutoffProduct)
    (hconv : massLocalInverseProductTendsTo L cutoffProduct)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    let V := L.rationalQuadraticSpaceMatrix
    let D := cliffordSpinCandidateRawOnoTamagawaDataOfLattice
      L (by omega) inst hcutoffProduct hconv
    let horizontalScalar :=
      L.periodizedHorizontalRawSOFiberHaarBoundRightHaarScalar
        (by omega) inst hcutoffProduct hconv
    (horizontalScalar : ℝ≥0∞) *
        (∫⁻ Z,
          f (V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule Z)
        ∂(V.fullAdelicCliffordGeneralSpinHorizontalMeasurableWeilData
          |>.quotientMeasure)) =
      rationalIdeleClassLogCutoffLIntegral f *
        D.spinTamagawaNumberENNReal := by
  let V := L.rationalQuadraticSpaceMatrix
  let D := cliffordSpinCandidateRawOnoTamagawaDataOfLattice
    L (by omega : 3 ≤ r + 2) inst hcutoffProduct hconv
  let horizontalScalar :=
    L.periodizedHorizontalRawSOFiberHaarBoundRightHaarScalar
      (by omega : 3 ≤ r + 2) inst hcutoffProduct hconv
  let mu :=
    V.fullAdelicCliffordGeneralSpinHorizontalMeasurableWeilData.quotientMeasure
  let cutoff : V.FullAdelicCliffordGeneralSpinLeftQuotient → ℝ≥0∞ :=
    fun Z ↦ f (V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule Z)
  have hmeasure :
      L.horizontalRawSOFiberHaarBoundMeasure inst D =
        horizontalScalar • mu := by
    simpa only [D, horizontalScalar, V, mu] using
      L.horizontalRawSOFiberHaarBoundMeasure_eq_smul_horizontalQuotientMeasure
        (by omega) inst hcutoffProduct hconv
  have hrelative : D.IsOnoRelativeTamagawaComparison := by
    simpa only [D] using
      L.cliffordSpinCandidateRawOnoTamagawaDataOfLattice_isOnoRelativeComparison
        (by omega) inst hcutoffProduct hconv
  have hSO :
      D.specialOrthogonalData.tamagawaNumberENNReal =
        2 * D.spinTamagawaNumberENNReal :=
    D.specialOrthogonalTamagawaNumberENNReal_eq_two_mul_spin_of_onoRelativeComparison
      hrelative
  change
    (horizontalScalar : ℝ≥0∞) * (∫⁻ Z, cutoff Z ∂mu) =
      rationalIdeleClassLogCutoffLIntegral f *
        D.spinTamagawaNumberENNReal
  calc
    (horizontalScalar : ℝ≥0∞) * (∫⁻ Z, cutoff Z ∂mu) =
        ∫⁻ Z, cutoff Z ∂horizontalScalar • mu := by
      rw [lintegral_smul_measure]
      rfl
    _ = ∫⁻ Z, cutoff Z ∂L.horizontalRawSOFiberHaarBoundMeasure inst D := by
      rw [hmeasure]
    _ = D.horizontalCrossedLogCutoffLIntegral V
          (fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal_surjective L)
          f := by
      exact L.horizontalRawSOFiberHaarBoundMeasure_lintegral_logCutoff
        inst D f hf
    _ = V.horizontalFiberLogCutoffLIntegral
          (V.fullAdelicCliffordGeneralSpinLeftQuotientMap 1) f *
          D.specialOrthogonalData.tamagawaNumberENNReal := by
      rw [D.horizontalCrossedLogCutoffLIntegral_eq V
        (fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal_surjective L)
        f hf]
    _ = ((2 : ℝ≥0∞)⁻¹ * rationalIdeleClassLogCutoffLIntegral f) *
          D.specialOrthogonalData.tamagawaNumberENNReal := by
      rw [V.horizontalFiberLogCutoffLIntegral_one f hf]
      change rationalIdeleClassLogCutoffLIntegral (fun t ↦ f (2 * t)) *
          D.specialOrthogonalData.tamagawaNumberENNReal = _
      rw [rationalIdeleClassLogCutoffLIntegral_two_mul f hf]
    _ = ((2 : ℝ≥0∞)⁻¹ * rationalIdeleClassLogCutoffLIntegral f) *
          (2 * D.spinTamagawaNumberENNReal) := by rw [hSO]
    _ = rationalIdeleClassLogCutoffLIntegral f *
          D.spinTamagawaNumberENNReal := by
      calc
        ((2 : ℝ≥0∞)⁻¹ * rationalIdeleClassLogCutoffLIntegral f) *
            (2 * D.spinTamagawaNumberENNReal) =
          ((2 : ℝ≥0∞)⁻¹ * 2) *
            (rationalIdeleClassLogCutoffLIntegral f *
              D.spinTamagawaNumberENNReal) := by ac_rfl
        _ = rationalIdeleClassLogCutoffLIntegral f *
              D.spinTamagawaNumberENNReal := by
          rw [ENNReal.inv_mul_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
            (by norm_num : (2 : ℝ≥0∞) ≠ ⊤), one_mul]

end PositiveDefiniteIntegralLattice

end
