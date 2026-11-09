import SMSFormula.RationalCliffordGeneralSpinAllRationalThetaCalibration

/-!
# The cutoff-normalized quotient theta functional, with the Spin volume kept visible

The existing probability normalization divides the raw quotient theta cutoff integral by
`cutoffMass * spinVolume`, so its zero-orbit coefficient is exactly `Phi 0` and the ambient
Spin volume has been erased.  That normalization cannot be used to extract the volume: doing
so would be circular.

The alternative is to divide only by the known cutoff scalar.  This file does
that.  The resulting functional satisfies

```text
I_V(Phi) = t_V * Phi 0 + sum over represented nonzero norms of R_a(Phi),
```

with `t_V` the existing intrinsic Spin quantity, left explicit on the zero orbit.  Nothing here
evaluates `t_V`, and nothing here compares `R_a` with the Eisenstein side.

This is a renormalization of the existing expansion, not a new analytic input.
-/

noncomputable section

open MeasureTheory RationalQuadraticSpaceMatrix
open scoped ENNReal NNReal

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

/-- The CUTOFF-normalized ordinary theta functional: the raw horizontal cutoff integral
divided by the known cutoff scalar alone, so the ambient Spin volume stays visible. -/
noncomputable def cutoffNormalizedFullAdelicCliffordGeneralSpinTheta
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hr : 1 ≤ r)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {cutoffProduct : ℝ} (hcutoffProduct : 0 < cutoffProduct)
    (hconv : massLocalInverseProductTendsTo L cutoffProduct)
    (Phi : (Fin (r + 2) → RationalAdele) → ℝ≥0∞)
    (f : ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  let horizontalScalar :=
    L.periodizedHorizontalRawSOFiberHaarBoundRightHaarScalar
      (by omega) inst hcutoffProduct hconv
  ((horizontalScalar : ℝ≥0∞) *
      L.fullAdelicCliffordGeneralSpinThetaLogCutoffIntegral Phi f) /
    rationalIdeleClassLogCutoffLIntegral f

/-- The cutoff-normalized contribution of one represented nonzero rational norm. -/
noncomputable def cutoffNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hr : 1 ≤ r)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {cutoffProduct : ℝ} (hcutoffProduct : 0 < cutoffProduct)
    (hconv : massLocalInverseProductTendsTo L cutoffProduct)
    (a : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm)
    (Phi : (Fin (r + 2) → RationalAdele) → ℝ≥0∞)
    (f : ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  let horizontalScalar :=
    L.periodizedHorizontalRawSOFiberHaarBoundRightHaarScalar
      (by omega) inst hcutoffProduct hconv
  ((horizontalScalar : ℝ≥0∞) *
      L.fullAdelicCliffordGeneralSpinRepresentedNormThetaLogCutoffIntegral
        a Phi f) /
    rationalIdeleClassLogCutoffLIntegral f

/-- The target shape.  The zero-orbit coefficient of the cutoff-normalized functional is the
existing intrinsic Spin quantity, not one. -/
theorem cutoffNormalizedFullAdelicCliffordGeneralSpinTheta_eq_spinVolume_add_representedNorm
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
    L.cutoffNormalizedFullAdelicCliffordGeneralSpinTheta
        hr inst hcutoffProduct hconv Phi f =
      (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
          L (by omega) inst hcutoffProduct hconv).spinTamagawaNumberENNReal * Phi 0 +
        ∑' a : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm,
          L.cutoffNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta
            hr inst hcutoffProduct hconv a Phi f := by
  classical
  set V := L.rationalQuadraticSpaceMatrix with hV
  set horizontalScalar :=
    L.periodizedHorizontalRawSOFiberHaarBoundRightHaarScalar
      (by omega : 3 ≤ r + 2) inst hcutoffProduct hconv with hhs
  set cutoffMass := rationalIdeleClassLogCutoffLIntegral f with hcm
  set spinVolume := (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
    L (by omega : 3 ≤ r + 2) inst hcutoffProduct hconv).spinTamagawaNumberENNReal with hsv
  set zeroIntegral : ℝ≥0∞ :=
    ∫⁻ Z, f (V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule Z)
      ∂(V.fullAdelicCliffordGeneralSpinHorizontalMeasurableWeilData
        |>.quotientMeasure) with hzi
  set totalIntegral := L.fullAdelicCliffordGeneralSpinThetaLogCutoffIntegral Phi f with hti
  set fiberIntegral := fun a : V.RepresentedNonzeroRationalNorm ↦
    L.fullAdelicCliffordGeneralSpinRepresentedNormThetaLogCutoffIntegral a Phi f with hfi
  have hdecomposition :
      totalIntegral = Phi 0 * zeroIntegral +
        ∑' a : V.RepresentedNonzeroRationalNorm, fiberIntegral a := by
    simpa only [hV, hti, hzi, hfi] using
      L.fullAdelicCliffordGeneralSpinThetaLogCutoffIntegral_eq_zero_add_representedNorm
        Phi hPhi f hf
  have hzero : (horizontalScalar : ℝ≥0∞) * zeroIntegral = cutoffMass * spinVolume := by
    simpa only [hV, hhs, hcm, hsv, hzi] using
      L.horizontalScalar_mul_lintegral_logCutoff_eq_cutoffMass_mul_spinTamagawa
        hr inst hcutoffProduct hconv f hf
  have htsumDiv :
      (∑' a : V.RepresentedNonzeroRationalNorm,
          (horizontalScalar : ℝ≥0∞) * fiberIntegral a) / cutoffMass =
        ∑' a : V.RepresentedNonzeroRationalNorm,
          ((horizontalScalar : ℝ≥0∞) * fiberIntegral a) / cutoffMass := by
    rw [div_eq_mul_inv, ← ENNReal.tsum_mul_right]
    simp only [div_eq_mul_inv]
  unfold cutoffNormalizedFullAdelicCliffordGeneralSpinTheta
  unfold cutoffNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta
  dsimp only
  change
    ((horizontalScalar : ℝ≥0∞) * totalIntegral) / cutoffMass =
      spinVolume * Phi 0 +
        ∑' a : V.RepresentedNonzeroRationalNorm,
          ((horizontalScalar : ℝ≥0∞) * fiberIntegral a) / cutoffMass
  have hzeroTerm :
      (horizontalScalar : ℝ≥0∞) * (Phi 0 * zeroIntegral) / cutoffMass =
        spinVolume * Phi 0 := by
    have : (horizontalScalar : ℝ≥0∞) * (Phi 0 * zeroIntegral) =
        Phi 0 * (cutoffMass * spinVolume) := by
      calc (horizontalScalar : ℝ≥0∞) * (Phi 0 * zeroIntegral)
          = Phi 0 * ((horizontalScalar : ℝ≥0∞) * zeroIntegral) := by ac_rfl
        _ = Phi 0 * (cutoffMass * spinVolume) := by rw [hzero]
    rw [this]
    rw [show Phi 0 * (cutoffMass * spinVolume) = (spinVolume * Phi 0) * cutoffMass by ac_rfl,
      mul_div_assoc, ENNReal.div_self hcutoffMass_ne_zero hcutoffMass_ne_top, mul_one]
  rw [hdecomposition, mul_add, ENNReal.add_div, hzeroTerm, ← ENNReal.tsum_mul_left, htsumDiv]

/-- `M_{V,kappa} = K_kappa * t_V`: the raw cutoff mass of the quotient, divided by the known
cutoff scalar, is exactly the existing intrinsic Spin quantity. -/
theorem quotientCutoffMass_div_cutoffMass_eq_spinVolume
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hr : 1 ≤ r)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {cutoffProduct : ℝ} (hcutoffProduct : 0 < cutoffProduct)
    (hconv : massLocalInverseProductTendsTo L cutoffProduct)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f)
    (hcutoffMass_ne_zero : rationalIdeleClassLogCutoffLIntegral f ≠ 0)
    (hcutoffMass_ne_top : rationalIdeleClassLogCutoffLIntegral f ≠ ⊤) :
    ((L.periodizedHorizontalRawSOFiberHaarBoundRightHaarScalar
          (by omega) inst hcutoffProduct hconv : ℝ≥0∞) *
        ∫⁻ Z, f (L.rationalQuadraticSpaceMatrix
            |>.fullAdelicCliffordGeneralSpinLeftQuotientLogModule Z)
          ∂(L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinHorizontalMeasurableWeilData
            |>.quotientMeasure)) / rationalIdeleClassLogCutoffLIntegral f =
      (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
        L (by omega) inst hcutoffProduct hconv).spinTamagawaNumberENNReal := by
  rw [L.horizontalScalar_mul_lintegral_logCutoff_eq_cutoffMass_mul_spinTamagawa
    hr inst hcutoffProduct hconv f hf, mul_comm, mul_div_assoc,
    ENNReal.div_self hcutoffMass_ne_zero hcutoffMass_ne_top, mul_one]

/-- The two normalizations differ exactly by the unknown volume: the probability version is
the cutoff version divided by it, which is why only the latter can expose it. -/
theorem probabilityNormalized_eq_cutoffNormalized_div_spinVolume
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hr : 1 ≤ r)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {cutoffProduct : ℝ} (hcutoffProduct : 0 < cutoffProduct)
    (hconv : massLocalInverseProductTendsTo L cutoffProduct)
    (Phi : (Fin (r + 2) → RationalAdele) → ℝ≥0∞)
    (f : ℝ → ℝ≥0∞)
    (hcutoffMass_ne_zero : rationalIdeleClassLogCutoffLIntegral f ≠ 0)
    (hcutoffMass_ne_top : rationalIdeleClassLogCutoffLIntegral f ≠ ⊤) :
    L.probabilityNormalizedFullAdelicCliffordGeneralSpinTheta
        hr inst hcutoffProduct hconv Phi f =
      L.cutoffNormalizedFullAdelicCliffordGeneralSpinTheta
          hr inst hcutoffProduct hconv Phi f /
        (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
          L (by omega) inst hcutoffProduct hconv).spinTamagawaNumberENNReal := by
  unfold probabilityNormalizedFullAdelicCliffordGeneralSpinTheta
  unfold cutoffNormalizedFullAdelicCliffordGeneralSpinTheta
  dsimp only
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv,
    ENNReal.mul_inv (Or.inl hcutoffMass_ne_zero) (Or.inl hcutoffMass_ne_top), ← mul_assoc]


end PositiveDefiniteIntegralLattice

end
