import SMSFormula.RationalCliffordGeneralSpinAllRationalThetaCalibration
import SMSFormula.RationalQuadraticIsometrySpinCandidateRepresentedNormOneShellCalibration

/-!
# Explicit orbital form of one normalized represented-norm contribution

The section-free normalized ordinary quotient theta contribution attached to
one represented nonzero rational norm can be evaluated through any supplied
local complement-lattice witness.  The exact formula retains the quotient of
the ambient and lower horizontal periodization scalars.  Neither scalar is
identified with the other, and the auxiliary ambient shell integral is not
declared witness-independent by itself.
-/

noncomputable section

open MeasureTheory RationalQuadraticSpaceMatrix
open scoped ENNReal NNReal

namespace PositiveDefiniteIntegralLattice

variable {r s : ℕ}

noncomputable local instance normalizedContributionTargetMeasurableSpace
    (V : RationalQuadraticSpaceMatrix (r + 2)) (x : Fin (r + 2) → ℚ) :
    MeasurableSpace (V.anisotropicRationalAmbientShell x RationalAdele) :=
  borel _

noncomputable local instance normalizedContributionTargetBorelSpace
    (V : RationalQuadraticSpaceMatrix (r + 2)) (x : Fin (r + 2) → ℚ) :
    BorelSpace (V.anisotropicRationalAmbientShell x RationalAdele) :=
  ⟨rfl⟩

/-- Exact local-witness evaluation of one intrinsic normalized nonzero norm
contribution.  The ambient-to-lower horizontal scalar ratio appears
explicitly. -/
theorem probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta_eq_horizontalRatio_mul_shell_mul_coefficient
    (A : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hr : 1 ≤ r)
    (instA : Fintype A.ConcreteProperRationalDoubleCosetSet)
    {ambientCutoffProduct : ℝ}
    (hAmbientCutoffProduct : 0 < ambientCutoffProduct)
    (hconvA : massLocalInverseProductTendsTo
      A ambientCutoffProduct)
    (L : PositiveDefiniteIntegralLattice (s + 2)) [Nonempty (Fin (s + 2))]
    (hs : 1 ≤ s)
    (instL : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {lowerCutoffProduct : ℝ}
    (hLowerCutoffProduct : 0 < lowerCutoffProduct)
    (hconvL : massLocalInverseProductTendsTo
      L lowerCutoffProduct)
    (a : A.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm)
    (x : a.rationalVectorFiber A.rationalQuadraticSpaceMatrix)
    (e : L.rationalQuadraticSpaceMatrix.quadraticForm.IsometryEquiv
      (A.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm
        |>.orthogonalRestriction x.1))
    (hLocal : A.rationalQuadraticSpaceMatrix
      |>.OneShellSpinCoefficientLocallyNonempty)
    (Phi : (Fin (r + 2) → RationalAdele) → ℝ≥0∞)
    (hPhi : Measurable Phi)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f)
    (hcutoffMass_ne_zero : rationalIdeleClassLogCutoffLIntegral f ≠ 0)
    (hcutoffMass_ne_top : rationalIdeleClassLogCutoffLIntegral f ≠ ⊤) :
    let V := A.rationalQuadraticSpaceMatrix
    let DAmbient := cliffordSpinCandidateRawOnoTamagawaDataOfLattice
      A (by omega) instA hAmbientCutoffProduct hconvA
    let P := integralLatticeAnisotropicComplementPresentation L V x.1 e
    let ambientHorizontalScalar :=
      A.periodizedHorizontalRawSOFiberHaarBoundRightHaarScalar
        (by omega) instA hAmbientCutoffProduct hconvA
    let lowerHorizontalScalar :=
      L.periodizedHorizontalRawSOFiberHaarBoundRightHaarScalar
        (by omega) instL hLowerCutoffProduct hconvL
    let ambientShellIntegral :=
      ∫⁻ y, Phi y.1 ∂P.anisotropicRationalAmbientShellMeasure
        (by rw [x.property]; exact a.property.1)
    A.probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta
        hr instA hAmbientCutoffProduct hconvA a Phi f =
      (((ambientHorizontalScalar : ℝ≥0∞) /
          (lowerHorizontalScalar : ℝ≥0∞)) * ambientShellIntegral) *
        V.representedNormOneShellSpinTamagawaCoefficient
          DAmbient hLocal a := by
  let V := A.rationalQuadraticSpaceMatrix
  let DAmbient := cliffordSpinCandidateRawOnoTamagawaDataOfLattice
    A (by omega : 3 ≤ r + 2) instA hAmbientCutoffProduct hconvA
  let P := integralLatticeAnisotropicComplementPresentation L V x.1 e
  let ambientHorizontalScalar :=
    A.periodizedHorizontalRawSOFiberHaarBoundRightHaarScalar
      (by omega : 3 ≤ r + 2) instA hAmbientCutoffProduct hconvA
  let lowerHorizontalScalar :=
    L.periodizedHorizontalRawSOFiberHaarBoundRightHaarScalar
      (by omega : 3 ≤ s + 2) instL hLowerCutoffProduct hconvL
  let ambientShellIntegral : ℝ≥0∞ :=
    ∫⁻ y, Phi y.1 ∂P.anisotropicRationalAmbientShellMeasure
      (by rw [x.property]; exact a.property.1)
  let intrinsicIntegral :=
    A.fullAdelicCliffordGeneralSpinRepresentedNormThetaLogCutoffIntegral
      a Phi f
  let cutoffMass := rationalIdeleClassLogCutoffLIntegral f
  let spinVolume := DAmbient.spinTamagawaNumberENNReal
  let denominator := cutoffMass * spinVolume
  let coefficient :=
    V.representedNormOneShellSpinTamagawaCoefficient DAmbient hLocal a
  have hrelative : DAmbient.IsOnoRelativeTamagawaComparison := by
    simpa only [DAmbient] using
      A.cliffordSpinCandidateRawOnoTamagawaDataOfLattice_isOnoRelativeComparison
        (by omega) instA hAmbientCutoffProduct hconvA
  have hspinVolume_ne_zero : spinVolume ≠ 0 :=
    DAmbient.spinTamagawaNumberENNReal_ne_zero
  have hspinVolume_ne_top : spinVolume ≠ ⊤ :=
    DAmbient.spinTamagawaNumberENNReal_ne_top_of_onoRelativeComparison
      hrelative
  have hdenominator_ne_zero : denominator ≠ 0 :=
    mul_ne_zero hcutoffMass_ne_zero hspinVolume_ne_zero
  have hdenominator_ne_top : denominator ≠ ⊤ :=
    ENNReal.mul_ne_top hcutoffMass_ne_top hspinVolume_ne_top
  have hlowerScalar_ne_zero : (lowerHorizontalScalar : ℝ≥0∞) ≠ 0 := by
    exact L.periodizedHorizontalRawSOFiberHaarBoundRightHaarScalar_ne_zero
      (by omega) instL hLowerCutoffProduct hconvL
  have hlowerScalar_ne_top : (lowerHorizontalScalar : ℝ≥0∞) ≠ ⊤ := by
    exact L.periodizedHorizontalRawSOFiberHaarBoundRightHaarScalar_ne_top
      (by omega) instL hLowerCutoffProduct hconvL
  have hcalibrated :
      ((lowerHorizontalScalar : ℝ≥0∞) * intrinsicIntegral) / spinVolume =
        (ambientShellIntegral * cutoffMass) * coefficient := by
    simpa only [V, DAmbient, P, lowerHorizontalScalar, ambientShellIntegral,
      intrinsicIntegral, cutoffMass, spinVolume, coefficient] using
      RationalQuadraticSpaceMatrix.integralLattice_lintegral_representedNormTheta_logCutoff_div_spinTamagawa_eq
        A L hs instL hLowerCutoffProduct hconvL a x e DAmbient hLocal
          Phi hPhi f hf
  have hcalibrated_mul :
      spinVolume * ((ambientShellIntegral * cutoffMass) * coefficient) =
        (lowerHorizontalScalar : ℝ≥0∞) * intrinsicIntegral :=
    (ENNReal.eq_div_iff hspinVolume_ne_zero hspinVolume_ne_top).mp
      hcalibrated.symm
  have hcross :
      denominator *
          ((((ambientHorizontalScalar : ℝ≥0∞) /
              (lowerHorizontalScalar : ℝ≥0∞)) * ambientShellIntegral) *
            coefficient) =
        (ambientHorizontalScalar : ℝ≥0∞) * intrinsicIntegral := by
    calc
      denominator *
          ((((ambientHorizontalScalar : ℝ≥0∞) /
              (lowerHorizontalScalar : ℝ≥0∞)) * ambientShellIntegral) *
            coefficient) =
          ((ambientHorizontalScalar : ℝ≥0∞) /
              (lowerHorizontalScalar : ℝ≥0∞)) *
            (spinVolume * ((ambientShellIntegral * cutoffMass) * coefficient)) := by
              dsimp only [denominator]
              ac_rfl
      _ = ((ambientHorizontalScalar : ℝ≥0∞) /
              (lowerHorizontalScalar : ℝ≥0∞)) *
            ((lowerHorizontalScalar : ℝ≥0∞) * intrinsicIntegral) := by
              rw [hcalibrated_mul]
      _ = ((((ambientHorizontalScalar : ℝ≥0∞) /
              (lowerHorizontalScalar : ℝ≥0∞)) *
            (lowerHorizontalScalar : ℝ≥0∞)) * intrinsicIntegral) := by
              ac_rfl
      _ = (ambientHorizontalScalar : ℝ≥0∞) * intrinsicIntegral := by
              rw [ENNReal.div_mul_cancel hlowerScalar_ne_zero
                hlowerScalar_ne_top]
  unfold probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta
  dsimp only
  change
    ((ambientHorizontalScalar : ℝ≥0∞) * intrinsicIntegral) / denominator =
      ((((ambientHorizontalScalar : ℝ≥0∞) /
          (lowerHorizontalScalar : ℝ≥0∞)) * ambientShellIntegral) *
        coefficient)
  exact ((ENNReal.eq_div_iff hdenominator_ne_zero hdenominator_ne_top).2
    hcross).symm

end PositiveDefiniteIntegralLattice

end
