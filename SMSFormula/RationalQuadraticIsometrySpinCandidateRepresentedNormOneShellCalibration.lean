import SMSFormula.RationalCliffordGeneralSpinRepresentedNormThetaQuotient

/-!
# Section-free represented-norm form of one-shell calibration

The intrinsic quotient integral attached directly to a represented nonzero
rational norm agrees with the vector-indexed ambient shell integral for every
supplied local complement-lattice witness.  Applying the closed ambient
one-shell theorem therefore identifies the intrinsic integral with the unique
section-free represented-norm Spin coefficient.

The presentation-dependent shell measure occurs only on the witness side of
the equality.  Its horizontally calibrated combination is forced by the
intrinsic quotient integral; the shell measure itself is not declared
witness-independent.  No vector, complement, presentation, raw datum, or
dependent witness family is selected.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory
open scoped ENNReal NNReal

namespace RationalQuadraticSpaceMatrix

variable {n r : ℕ}

noncomputable local instance representedNormCalibrationTargetMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) (x : Fin n → ℚ) :
    MeasurableSpace (V.anisotropicRationalAmbientShell x RationalAdele) :=
  borel _

noncomputable local instance representedNormCalibrationTargetBorelSpace
    (V : RationalQuadraticSpaceMatrix n) (x : Fin n → ℚ) :
    BorelSpace (V.anisotropicRationalAmbientShell x RationalAdele) :=
  ⟨rfl⟩

/-- Exact one-shell calibration with an intrinsic represented-norm quotient
integral and the unique section-free coefficient.  A supplied local witness
is used only to identify the corresponding horizontally normalized ambient
shell expression. -/
theorem integralLattice_lintegral_representedNormTheta_logCutoff_div_spinTamagawa_eq
    (A : PositiveDefiniteIntegralLattice n)
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hr : 1 ≤ r)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {cutoffProduct : ℝ} (hcutoffProduct : 0 < cutoffProduct)
    (hconv : massLocalInverseProductTendsTo L cutoffProduct)
    (a : A.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm)
    (x : a.rationalVectorFiber A.rationalQuadraticSpaceMatrix)
    (e : L.rationalQuadraticSpaceMatrix.quadraticForm.IsometryEquiv
      (A.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm
        |>.orthogonalRestriction x.1))
    (DAmbient : A.rationalQuadraticSpaceMatrix
      |>.CliffordSpinCandidateRawOnoTamagawaData)
    (hLocal : A.rationalQuadraticSpaceMatrix
      |>.OneShellSpinCoefficientLocallyNonempty)
    (Phi : (Fin n → RationalAdele) → ℝ≥0∞)
    (hPhi : Measurable Phi)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    let V := A.rationalQuadraticSpaceMatrix
    let P := integralLatticeAnisotropicComplementPresentation L V x.1 e
    let horizontalScalar :=
      L.periodizedHorizontalRawSOFiberHaarBoundRightHaarScalar
        (by omega) inst hcutoffProduct hconv
    let ambientShellIntegral :=
      ∫⁻ y, Phi y.1 ∂P.anisotropicRationalAmbientShellMeasure
        (by rw [x.property]; exact a.property.1)
    ((horizontalScalar : ℝ≥0∞) *
        A.fullAdelicCliffordGeneralSpinRepresentedNormThetaLogCutoffIntegral
          a Phi f) /
        DAmbient.spinTamagawaNumberENNReal =
      (ambientShellIntegral * rationalIdeleClassLogCutoffLIntegral f) *
        V.representedNormOneShellSpinTamagawaCoefficient
          DAmbient hLocal a := by
  let V := A.rationalQuadraticSpaceMatrix
  have hx : V.nativeRationalQuadraticForm x.1 ≠ 0 := by
    rw [x.property]
    exact a.property.1
  let P := integralLatticeAnisotropicComplementPresentation L V x.1 e
  let DLower := cliffordSpinCandidateRawOnoTamagawaDataOfLattice
    L (by omega : 3 ≤ r + 2) inst hcutoffProduct hconv
  let horizontalScalar :=
    L.periodizedHorizontalRawSOFiberHaarBoundRightHaarScalar
      (by omega : 3 ≤ r + 2) inst hcutoffProduct hconv
  let ambientShellIntegral : ℝ≥0∞ :=
    ∫⁻ y, Phi y.1 ∂P.anisotropicRationalAmbientShellMeasure hx
  let ambientThetaIntegral : ℝ≥0∞ :=
    ∫⁻ Z,
      f (V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule Z)
    ∂(V.fullAdelicCliffordGeneralSpinHorizontalMeasurableWeilData
      |>.quotientMeasure).withDensity
        (V.fullAdelicCliffordGeneralSpinRationalShellThetaOnLeftQuotient
          x.1 Phi)
  have hintrinsic :
      A.fullAdelicCliffordGeneralSpinRepresentedNormThetaLogCutoffIntegral
          a Phi f = ambientThetaIntegral := by
    unfold PositiveDefiniteIntegralLattice.fullAdelicCliffordGeneralSpinRepresentedNormThetaLogCutoffIntegral
    dsimp only [V, ambientThetaIntegral]
    have hdensity :
        V.fullAdelicCliffordGeneralSpinRepresentedNormThetaOnLeftQuotient
            a Phi =
          V.fullAdelicCliffordGeneralSpinRationalShellThetaOnLeftQuotient
            x.1 Phi := by
      funext Z
      exact
        V.fullAdelicCliffordGeneralSpinRepresentedNormThetaOnLeftQuotient_eq_rationalShellTheta
          a x Phi Z
    rw [hdensity]
  let w : a.OneShellSpinCoefficientWitness V :=
    { lowerRank := r + 2
      lowerLattice := L
      lowerRank_atLeastThree := by omega
      vector := x
      complementIsometry := e
      lowerRawData := DLower }
  have hcoefficient :
      P.oneShellSpinTamagawaCoefficient DLower DAmbient =
        V.representedNormOneShellSpinTamagawaCoefficient
          DAmbient hLocal a := by
    have hw := V.representedNormOneShellSpinTamagawaCoefficient_eq_witness
      DAmbient hLocal a w
    symm
    simpa only [RepresentedNonzeroRationalNorm.OneShellSpinCoefficientWitness.coefficient,
      RepresentedNonzeroRationalNorm.OneShellSpinCoefficientWitness.presentation,
      w, P] using hw
  have hcalibrated :=
    integralLattice_lintegral_ambientRationalShellTheta_logCutoff_div_spinTamagawa_eq
      L hr inst hcutoffProduct hconv V x.1 hx e DAmbient Phi hPhi f hf
  change
    ((horizontalScalar : ℝ≥0∞) *
        A.fullAdelicCliffordGeneralSpinRepresentedNormThetaLogCutoffIntegral
          a Phi f) /
        DAmbient.spinTamagawaNumberENNReal =
      (ambientShellIntegral * rationalIdeleClassLogCutoffLIntegral f) *
        V.representedNormOneShellSpinTamagawaCoefficient
          DAmbient hLocal a
  rw [hintrinsic, ← hcoefficient]
  simpa only [P, DLower, horizontalScalar, ambientThetaIntegral,
    ambientShellIntegral] using hcalibrated

end RationalQuadraticSpaceMatrix

end
