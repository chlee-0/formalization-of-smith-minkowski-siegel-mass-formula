import SMSFormula.RationalCliffordGeneralSpinThetaCutoffDomination
import SMSFormula.RationalCliffordGeneralSpinPolarGaussianLatticeCutoffFinite

/-!
# A bounded quotient theta already gives raw finiteness

The domination criterion compares tests, and that is too rigid for the Weyl transform, whose
finite carrier is the polar dual lattice.  The criterion needed for other carriers
compares thetas: whatever the test, if its quotient theta is bounded by a finite constant, the
raw cutoff integral against the existing unit cutoff is finite, and hence the whole
cutoff-normalized layer applies.

This is exactly the shape of the existing argument for the standard test -- bound the theta by
its proper-domain bound, then use the finite cutoff mass -- extracted so that any test can use
it.  For a new carrier, what is needed is therefore a uniform bound on its
quotient theta, nothing else.

Negative scope: no bound is supplied for any new test here.  In particular no bound is proved
for the polar-dual carrier; the proper-domain factorization that would produce one is not
carried out.
-/

noncomputable section

open MeasureTheory RationalQuadraticSpaceMatrix
open PositiveDefiniteIntegralLattice
open scoped ENNReal NNReal

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

/-- Raw finiteness from a bounded quotient theta, for the existing unit cutoff. -/
theorem fullAdelicCliffordGeneralSpinThetaLogCutoffIntegral_unit_ne_top_of_thetaOnLeftQuotient_le
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hr : 1 ≤ r)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {cutoffProduct : ℝ} (hcutoffProduct : 0 < cutoffProduct)
    (hconv : massLocalInverseProductTendsTo L cutoffProduct)
    (Phi : (Fin (r + 2) → RationalAdele) → ℝ≥0∞)
    {B : ℝ≥0∞} (hB : B ≠ ⊤)
    (hle : ∀ Z, (L.rationalQuadraticSpaceMatrix).fullAdelicCliffordGeneralSpinThetaOnLeftQuotient
      Phi Z ≤ B) :
    L.fullAdelicCliffordGeneralSpinThetaLogCutoffIntegral Phi
        rationalIdeleClassUnitLogCutoff ≠ ⊤ := by
  have hbare : (∫⁻ Z, rationalIdeleClassUnitLogCutoff
        ((L.rationalQuadraticSpaceMatrix).fullAdelicCliffordGeneralSpinLeftQuotientLogModule Z)
      ∂((L.rationalQuadraticSpaceMatrix).fullAdelicCliffordGeneralSpinHorizontalMeasurableWeilData
          |>.quotientMeasure)) ≠ ⊤ :=
    L.lintegral_horizontalQuotient_unitLogCutoff_ne_top hr inst hcutoffProduct hconv
  have hmono : L.fullAdelicCliffordGeneralSpinThetaLogCutoffIntegral Phi
        rationalIdeleClassUnitLogCutoff ≤
      B * (∫⁻ Z, rationalIdeleClassUnitLogCutoff
          ((L.rationalQuadraticSpaceMatrix).fullAdelicCliffordGeneralSpinLeftQuotientLogModule Z)
        ∂((L.rationalQuadraticSpaceMatrix).fullAdelicCliffordGeneralSpinHorizontalMeasurableWeilData
            |>.quotientMeasure)) := by
    unfold fullAdelicCliffordGeneralSpinThetaLogCutoffIntegral
    dsimp only
    calc (∫⁻ Z, rationalIdeleClassUnitLogCutoff _
            ∂(_ : Measure _).withDensity
              ((L.rationalQuadraticSpaceMatrix).fullAdelicCliffordGeneralSpinThetaOnLeftQuotient
                Phi))
        ≤ ∫⁻ Z, rationalIdeleClassUnitLogCutoff
            ((L.rationalQuadraticSpaceMatrix).fullAdelicCliffordGeneralSpinLeftQuotientLogModule Z)
          ∂(((L.rationalQuadraticSpaceMatrix).fullAdelicCliffordGeneralSpinHorizontalMeasurableWeilData
              |>.quotientMeasure).withDensity (fun _ => B)) := by
          refine lintegral_mono' (withDensity_mono (Filter.Eventually.of_forall hle)) le_rfl
      _ = B * _ := by
          rw [withDensity_const, lintegral_smul_measure, smul_eq_mul]
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top hB hbare) hmono

/-- Hence the cutoff-normalized functional is finite for any test with a bounded quotient
theta, so the expansion and the real-valued form apply to it. -/
theorem cutoffNormalizedFullAdelicCliffordGeneralSpinTheta_unit_ne_top_of_thetaOnLeftQuotient_le
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hr : 1 ≤ r)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {cutoffProduct : ℝ} (hcutoffProduct : 0 < cutoffProduct)
    (hconv : massLocalInverseProductTendsTo L cutoffProduct)
    (Phi : (Fin (r + 2) → RationalAdele) → ℝ≥0∞)
    {B : ℝ≥0∞} (hB : B ≠ ⊤)
    (hle : ∀ Z, (L.rationalQuadraticSpaceMatrix).fullAdelicCliffordGeneralSpinThetaOnLeftQuotient
      Phi Z ≤ B) :
    L.cutoffNormalizedFullAdelicCliffordGeneralSpinTheta hr inst hcutoffProduct hconv Phi
        rationalIdeleClassUnitLogCutoff ≠ ⊤ :=
  L.cutoffNormalizedFullAdelicCliffordGeneralSpinTheta_ne_top hr inst hcutoffProduct hconv _ _
    rationalIdeleClassLogCutoffLIntegral_unit_ne_zero
    (L.fullAdelicCliffordGeneralSpinThetaLogCutoffIntegral_unit_ne_top_of_thetaOnLeftQuotient_le
      hr inst hcutoffProduct hconv Phi hB hle)

end PositiveDefiniteIntegralLattice

end
