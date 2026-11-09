import SMSFormula.RationalQuadraticIsometryGeneralSpinHorizontalThetaLogCutoffTransport
import SMSFormula.RationalQuadraticIsometryGeneralSpinFullAdelicShellMeasureTransport
import SMSFormula.RationalQuadraticIsometrySpinCandidateOneShellCoefficient

/-!
# Ambient calibration of one rational Spin shell

For one supplied lattice-backed complement presentation, the calibrated block
one-shell identity is transported simultaneously on its shell and quotient
coordinates.  Both sides acquire the same positive finite horizontal
presentation scalar.  Cancelling only that scalar gives an intrinsic ambient
identity, and division by the supplied ambient Spin volume retains the exact
lower/ambient Spin Tamagawa ratio.

The ordinary ambient quotient theta density remains unweighted.  The common
idele-class cutoff mass and the horizontal calibration scalar remain visible.
No shell representative, complement lattice, global witness family, new
measure, or chart is selected.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open MeasureTheory
open scoped ENNReal NNReal

namespace RationalQuadraticSpaceMatrix

variable {n r : ℕ}

noncomputable local instance ambientOneShellCalibrationTargetMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) (x : Fin n → ℚ) :
    MeasurableSpace (V.anisotropicRationalAmbientShell x RationalAdele) :=
  borel _

noncomputable local instance ambientOneShellCalibrationTargetBorelSpace
    (V : RationalQuadraticSpaceMatrix n) (x : Fin n → ℚ) :
    BorelSpace (V.anisotropicRationalAmbientShell x RationalAdele) :=
  ⟨rfl⟩

noncomputable local instance ambientOneShellCalibrationBlockMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace
      (L.rationalQuadraticSpaceMatrix
        |>.nonisotropicLastQuadraticShell a ha RationalAdele) :=
  L.rationalQuadraticSpaceMatrix
    |>.fullAdelicShellMeasurableWeilTargetMeasurableSpace a ha

noncomputable local instance ambientOneShellCalibrationBlockBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix
        |>.nonisotropicLastQuadraticShell a ha RationalAdele) :=
  L.rationalQuadraticSpaceMatrix
    |>.fullAdelicShellMeasurableWeilTargetBorelSpace a ha

/-- Exact ambient one-shell calibration attached to one supplied complement
witness.  The left side is the horizontally calibrated ordinary shell-theta
integral divided by the ambient Spin volume; the right side retains the
ambient shell integral, common logarithmic cutoff mass, and literal
lower/ambient Spin Tamagawa coefficient. -/
theorem integralLattice_lintegral_ambientRationalShellTheta_logCutoff_div_spinTamagawa_eq
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hr : 1 ≤ r)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {cutoffProduct : ℝ} (hcutoffProduct : 0 < cutoffProduct)
    (hconv : massLocalInverseProductTendsTo L cutoffProduct)
    (V : RationalQuadraticSpaceMatrix n) (x : Fin n → ℚ)
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (e : L.rationalQuadraticSpaceMatrix.quadraticForm.IsometryEquiv
      (V.nativeRationalQuadraticForm.orthogonalRestriction x))
    (DAmbient : V.CliffordSpinCandidateRawOnoTamagawaData)
    (Phi : (Fin n → RationalAdele) → ℝ≥0∞)
    (hPhi : Measurable Phi)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    let P := integralLatticeAnisotropicComplementPresentation L V x e
    let DLower := cliffordSpinCandidateRawOnoTamagawaDataOfLattice
      L (by omega) inst hcutoffProduct hconv
    let horizontalScalar :=
      L.periodizedHorizontalRawSOFiberHaarBoundRightHaarScalar
        (by omega) inst hcutoffProduct hconv
    let ambientThetaIntegral :=
      ∫⁻ Z,
        f (V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule Z)
      ∂(V.fullAdelicCliffordGeneralSpinHorizontalMeasurableWeilData
        |>.quotientMeasure).withDensity
          (V.fullAdelicCliffordGeneralSpinRationalShellThetaOnLeftQuotient
            x Phi)
    let ambientShellIntegral :=
      ∫⁻ y, Phi y.1 ∂P.anisotropicRationalAmbientShellMeasure hx
    ((horizontalScalar : ℝ≥0∞) * ambientThetaIntegral) /
        DAmbient.spinTamagawaNumberENNReal =
      (ambientShellIntegral * rationalIdeleClassLogCutoffLIntegral f) *
        P.oneShellSpinTamagawaCoefficient DLower DAmbient := by
  let P := integralLatticeAnisotropicComplementPresentation L V x e
  let DLower := cliffordSpinCandidateRawOnoTamagawaDataOfLattice
    L (by omega : 3 ≤ r + 2) inst hcutoffProduct hconv
  let horizontalScalar :=
    L.periodizedHorizontalRawSOFiberHaarBoundRightHaarScalar
      (by omega : 3 ≤ r + 2) inst hcutoffProduct hconv
  let presentationScalar : ℝ≥0∞ :=
    P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar hx
  let ambientThetaIntegral : ℝ≥0∞ :=
    ∫⁻ Z,
      f (V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule Z)
    ∂(V.fullAdelicCliffordGeneralSpinHorizontalMeasurableWeilData
      |>.quotientMeasure).withDensity
        (V.fullAdelicCliffordGeneralSpinRationalShellThetaOnLeftQuotient
          x Phi)
  let ambientShellIntegral : ℝ≥0∞ :=
    ∫⁻ y, Phi y.1 ∂P.anisotropicRationalAmbientShellMeasure hx
  let cutoffMass := rationalIdeleClassLogCutoffLIntegral f
  have hPhiShell : Measurable
      (fun y : V.anisotropicRationalAmbientShell x RationalAdele ↦ Phi y.1) :=
    hPhi.comp continuous_subtype_val.measurable
  have hphiBlockDefault :
      @Measurable
        (L.rationalQuadraticSpaceMatrix
          |>.nonisotropicLastQuadraticShell
            (V.nativeRationalQuadraticForm x) hx RationalAdele)
        ℝ≥0∞ Subtype.instMeasurableSpace ENNReal.measurableSpace
        (fun y ↦ Phi
          (P.blockToAmbientShellHomeomorph hx RationalAdele y).1) :=
    hPhi.comp
      (continuous_subtype_val.comp
        (P.blockToAmbientShellHomeomorph hx RationalAdele).continuous).measurable
  have hphiBlock : Measurable
      (fun y : L.rationalQuadraticSpaceMatrix
          |>.nonisotropicLastQuadraticShell
            (V.nativeRationalQuadraticForm x) hx RationalAdele ↦
        Phi (P.blockToAmbientShellHomeomorph hx RationalAdele y).1) := by
    change @Measurable
      (L.rationalQuadraticSpaceMatrix
        |>.nonisotropicLastQuadraticShell
          (V.nativeRationalQuadraticForm x) hx RationalAdele)
      ℝ≥0∞ (borel _) ENNReal.measurableSpace _
    rw [← @BorelSpace.measurable_eq
      (L.rationalQuadraticSpaceMatrix
        |>.nonisotropicLastQuadraticShell
          (V.nativeRationalQuadraticForm x) hx RationalAdele)
      _ Subtype.instMeasurableSpace _]
    exact hphiBlockDefault
  have hshell :
      (∫⁻ y,
          Phi (P.blockToAmbientShellHomeomorph hx RationalAdele y).1
        ∂L.rationalQuadraticSpaceMatrix.fullAdelicNonisotropicLastShellMeasure
          (V.nativeRationalQuadraticForm x) hx) =
        presentationScalar * ambientShellIntegral := by
    exact
      P.lintegral_fullAdelicNonisotropicLastShellMeasure_eq_mul_ambient
        hx (fun y ↦ Phi y.1) hPhiShell
  have htheta :
      (∫⁻ C,
          f ((L.rationalQuadraticSpaceMatrix.nonisotropicLastExtension
              (V.nativeRationalQuadraticForm x) hx
            ).fullAdelicCliffordGeneralSpinLeftQuotientLogModule C)
        ∂(L.rationalQuadraticSpaceMatrix
          |>.fullAdelicNonisotropicLastHorizontalThetaCutoffMeasure
              (V.nativeRationalQuadraticForm x) hx
              (fun y ↦ Phi
                (P.blockToAmbientShellHomeomorph hx RationalAdele y).1))) =
        presentationScalar * ambientThetaIntegral := by
    change
      (∫⁻ C,
          f ((P.blockSpace hx
            ).fullAdelicCliffordGeneralSpinLeftQuotientLogModule C)
        ∂(L.rationalQuadraticSpaceMatrix
          |>.fullAdelicNonisotropicLastHorizontalThetaCutoffMeasure
              (V.nativeRationalQuadraticForm x) hx
              (fun y ↦ Phi
                (P.blockToAmbientShellHomeomorph hx RationalAdele y).1))) =
        presentationScalar * ambientThetaIntegral
    exact
      P.lintegral_fullAdelicNonisotropicLastHorizontalThetaCutoffMeasure_logCutoff_eq_ambient
        hx Phi hPhi f hf
  have hcalibrated :
      horizontalScalar * presentationScalar * ambientThetaIntegral =
        presentationScalar * ambientShellIntegral * cutoffMass *
          DLower.spinTamagawaNumberENNReal := by
    have h :=
      L.lintegral_fullAdelicNonisotropicLastCalibratedHorizontalThetaCutoffMeasure_logCutoff_eq
        hr inst hcutoffProduct hconv
        (V.nativeRationalQuadraticForm x) hx
        (fun y ↦ Phi
          (P.blockToAmbientShellHomeomorph hx RationalAdele y).1)
        hphiBlock f hf
    dsimp only at h
    rw [fullAdelicNonisotropicLastCalibratedHorizontalThetaCutoffMeasure,
      lintegral_smul_measure] at h
    change
      horizontalScalar *
          (∫⁻ C,
            f ((L.rationalQuadraticSpaceMatrix.nonisotropicLastExtension
                (V.nativeRationalQuadraticForm x) hx
              ).fullAdelicCliffordGeneralSpinLeftQuotientLogModule C)
          ∂(L.rationalQuadraticSpaceMatrix
            |>.fullAdelicNonisotropicLastHorizontalThetaCutoffMeasure
                (V.nativeRationalQuadraticForm x) hx
                (fun y ↦ Phi
                  (P.blockToAmbientShellHomeomorph hx RationalAdele y).1))) =
        (∫⁻ y,
            Phi (P.blockToAmbientShellHomeomorph hx RationalAdele y).1
          ∂L.rationalQuadraticSpaceMatrix.fullAdelicNonisotropicLastShellMeasure
            (V.nativeRationalQuadraticForm x) hx) *
          cutoffMass * DLower.spinTamagawaNumberENNReal at h
    rw [htheta, hshell] at h
    simpa only [mul_assoc] using h
  have hpresentationScalar_ne_zero : presentationScalar ≠ 0 := by
    exact ENNReal.coe_ne_zero.mpr
      (ne_of_gt (P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar_pos hx))
  have hpresentationScalar_ne_top : presentationScalar ≠ ∞ := by
    exact ENNReal.coe_ne_top
  have hcancelled :
      horizontalScalar * ambientThetaIntegral =
        ambientShellIntegral * cutoffMass *
          DLower.spinTamagawaNumberENNReal := by
    have hcommon :
        presentationScalar * (horizontalScalar * ambientThetaIntegral) =
          presentationScalar *
            (ambientShellIntegral * cutoffMass *
              DLower.spinTamagawaNumberENNReal) := by
      calc
        presentationScalar * (horizontalScalar * ambientThetaIntegral) =
            horizontalScalar * presentationScalar * ambientThetaIntegral := by
          ac_rfl
        _ = presentationScalar * ambientShellIntegral * cutoffMass *
              DLower.spinTamagawaNumberENNReal := hcalibrated
        _ = presentationScalar *
            (ambientShellIntegral * cutoffMass *
              DLower.spinTamagawaNumberENNReal) := by
          ac_rfl
    have h := congrArg (fun z : ℝ≥0∞ ↦ presentationScalar⁻¹ * z) hcommon
    simpa only [← mul_assoc,
      ENNReal.inv_mul_cancel hpresentationScalar_ne_zero
        hpresentationScalar_ne_top,
      one_mul] using h
  change
    (horizontalScalar * ambientThetaIntegral) /
        DAmbient.spinTamagawaNumberENNReal =
      (ambientShellIntegral * cutoffMass) *
        (DLower.spinTamagawaNumberENNReal /
          DAmbient.spinTamagawaNumberENNReal)
  rw [hcancelled, mul_div_assoc]

end RationalQuadraticSpaceMatrix

end
