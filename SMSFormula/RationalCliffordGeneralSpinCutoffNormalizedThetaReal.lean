import SMSFormula.RationalCliffordGeneralSpinCutoffNormalizedTheta

/-!
# Finiteness before `ENNReal.toReal`, and the real-valued expansion

The cutoff-normalized expansion `I_V(Phi) = t_V * Phi 0 + sum_a R_a(Phi)` lives in `ℝ≥0∞`.
Passing to a real- or complex-valued functional means applying `ENNReal.toReal`, and that
conversion silently loses an infinite quantity: `(⊤ : ℝ≥0∞).toReal = 0`.  So the finiteness
must be established first.

It is, from one genuine analytic hypothesis: the raw theta cutoff integral is finite.  The
horizontal scalar is an `NNReal` coercion, hence never `⊤`, and dividing by a nonzero cutoff
scalar cannot create `⊤`.  Finiteness of the whole functional then forces finiteness of both
terms of the expansion, since they are nonnegative, and the expansion transfers to `toReal`.

Negative scope: the finiteness hypothesis is about the raw integral of the chosen test, not
about the missing shell comparison.  Nothing here evaluates `t_V`, compares `R_a` with the
Eisenstein side, or supplies convergence for any particular test.
-/

noncomputable section

open MeasureTheory RationalQuadraticSpaceMatrix
open scoped ENNReal NNReal

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

/-- The cutoff-normalized functional is finite as soon as the raw cutoff integral is. -/
theorem cutoffNormalizedFullAdelicCliffordGeneralSpinTheta_ne_top
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hr : 1 ≤ r)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {cutoffProduct : ℝ} (hcutoffProduct : 0 < cutoffProduct)
    (hconv : massLocalInverseProductTendsTo L cutoffProduct)
    (Phi : (Fin (r + 2) → RationalAdele) → ℝ≥0∞)
    (f : ℝ → ℝ≥0∞)
    (hcutoffMass_ne_zero : rationalIdeleClassLogCutoffLIntegral f ≠ 0)
    (htotal : L.fullAdelicCliffordGeneralSpinThetaLogCutoffIntegral Phi f ≠ ⊤) :
    L.cutoffNormalizedFullAdelicCliffordGeneralSpinTheta
        hr inst hcutoffProduct hconv Phi f ≠ ⊤ := by
  unfold cutoffNormalizedFullAdelicCliffordGeneralSpinTheta
  dsimp only
  exact ENNReal.div_ne_top (ENNReal.mul_ne_top
    (L.periodizedHorizontalRawSOFiberHaarBoundRightHaarScalar_ne_top
      (by omega) inst hcutoffProduct hconv) htotal) hcutoffMass_ne_zero

/-- Both terms of the expansion are then finite, being nonnegative summands of a finite sum. -/
theorem cutoffNormalizedFullAdelicCliffordGeneralSpinTheta_terms_ne_top
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hr : 1 ≤ r)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {cutoffProduct : ℝ} (hcutoffProduct : 0 < cutoffProduct)
    (hconv : massLocalInverseProductTendsTo L cutoffProduct)
    (Phi : (Fin (r + 2) → RationalAdele) → ℝ≥0∞)
    (hPhi : Measurable Phi)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f)
    (hcutoffMass_ne_zero : rationalIdeleClassLogCutoffLIntegral f ≠ 0)
    (hcutoffMass_ne_top : rationalIdeleClassLogCutoffLIntegral f ≠ ⊤)
    (htotal : L.fullAdelicCliffordGeneralSpinThetaLogCutoffIntegral Phi f ≠ ⊤) :
    (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
          L (by omega) inst hcutoffProduct hconv).spinTamagawaNumberENNReal * Phi 0 ≠ ⊤ ∧
      (∑' a : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm,
        L.cutoffNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta
          hr inst hcutoffProduct hconv a Phi f) ≠ ⊤ := by
  have hfin := L.cutoffNormalizedFullAdelicCliffordGeneralSpinTheta_ne_top
    hr inst hcutoffProduct hconv Phi f hcutoffMass_ne_zero htotal
  rw [L.cutoffNormalizedFullAdelicCliffordGeneralSpinTheta_eq_spinVolume_add_representedNorm
    hr inst hcutoffProduct hconv Phi hPhi f hf hcutoffMass_ne_zero hcutoffMass_ne_top] at hfin
  exact ENNReal.add_ne_top.mp hfin

/-- The test value at the origin is finite too, because the Spin quantity is nonzero. -/
theorem zero_value_ne_top_of_cutoffNormalized_ne_top
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hr : 1 ≤ r)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {cutoffProduct : ℝ} (hcutoffProduct : 0 < cutoffProduct)
    (hconv : massLocalInverseProductTendsTo L cutoffProduct)
    (Phi : (Fin (r + 2) → RationalAdele) → ℝ≥0∞)
    (hPhi : Measurable Phi)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f)
    (hcutoffMass_ne_zero : rationalIdeleClassLogCutoffLIntegral f ≠ 0)
    (hcutoffMass_ne_top : rationalIdeleClassLogCutoffLIntegral f ≠ ⊤)
    (htotal : L.fullAdelicCliffordGeneralSpinThetaLogCutoffIntegral Phi f ≠ ⊤) :
    Phi 0 ≠ ⊤ := by
  obtain ⟨hzero, -⟩ := L.cutoffNormalizedFullAdelicCliffordGeneralSpinTheta_terms_ne_top
    hr inst hcutoffProduct hconv Phi hPhi f hf hcutoffMass_ne_zero hcutoffMass_ne_top htotal
  intro hcon
  exact hzero (by
    rw [hcon, ENNReal.mul_top (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
      L (by omega) inst hcutoffProduct hconv).spinTamagawaNumberENNReal_ne_zero])

/-- The real-valued expansion, after the finiteness is in hand. -/
theorem toReal_cutoffNormalizedFullAdelicCliffordGeneralSpinTheta_eq
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hr : 1 ≤ r)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {cutoffProduct : ℝ} (hcutoffProduct : 0 < cutoffProduct)
    (hconv : massLocalInverseProductTendsTo L cutoffProduct)
    (Phi : (Fin (r + 2) → RationalAdele) → ℝ≥0∞)
    (hPhi : Measurable Phi)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f)
    (hcutoffMass_ne_zero : rationalIdeleClassLogCutoffLIntegral f ≠ 0)
    (hcutoffMass_ne_top : rationalIdeleClassLogCutoffLIntegral f ≠ ⊤)
    (htotal : L.fullAdelicCliffordGeneralSpinThetaLogCutoffIntegral Phi f ≠ ⊤) :
    (L.cutoffNormalizedFullAdelicCliffordGeneralSpinTheta
        hr inst hcutoffProduct hconv Phi f).toReal =
      (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
          L (by omega) inst hcutoffProduct hconv).spinTamagawaNumberENNReal.toReal *
          (Phi 0).toReal +
        (∑' a : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm,
          L.cutoffNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta
            hr inst hcutoffProduct hconv a Phi f).toReal := by
  obtain ⟨hzero, htsum⟩ := L.cutoffNormalizedFullAdelicCliffordGeneralSpinTheta_terms_ne_top
    hr inst hcutoffProduct hconv Phi hPhi f hf hcutoffMass_ne_zero hcutoffMass_ne_top htotal
  rw [L.cutoffNormalizedFullAdelicCliffordGeneralSpinTheta_eq_spinVolume_add_representedNorm
    hr inst hcutoffProduct hconv Phi hPhi f hf hcutoffMass_ne_zero hcutoffMass_ne_top,
    ENNReal.toReal_add hzero htsum, ENNReal.toReal_mul]

end PositiveDefiniteIntegralLattice

end
