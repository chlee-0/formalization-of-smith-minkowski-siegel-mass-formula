import SMSFormula.RationalCliffordGeneralSpinVerticalFiberQuotientPeriodized
import SMSFormula.RationalIdeleDifferentialPositiveWeil
import SMSFormula.RationalIdeleClassDifferentialWeilComparison

/-!
# Positive-idele Weil form of the vertical Spin bind

The independently chosen rational idele-class Haar is replaced by its exact
positive-idele differential Weil presentation.  Pulling the already descended
vertical Spin kernel back along the literal positive-idele class map gives a
genuine measurable kernel, and the original vertical bind is the explicit
class-Haar conversion scalar times its differential positive-idele bind.

The final theorem inserts this equality into the section-free ambient
periodization and unfolds the translated raw Spin quotient.  This is the
outer Weil step needed by the remaining carrier-restricted Spin/idele
assembly.  No representative is made measurable, no Spin Weil identity is
used, and no normalization coefficient is set to one.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open MeasureTheory
open scoped ENNReal ProbabilityTheory

namespace RationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 700000
set_option maxHeartbeats 2000000

/-- The descended vertical Spin kernel pulled back to the positive-idele
differential fundamental domain. -/
noncomputable def verticalSpinFiberKernelAtPositiveIdele
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass) :
    ProbabilityTheory.Kernel
      positiveRationalAdeleUnitsSubgroup
      L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinLeftQuotient :=
  ⟨fun a => D.verticalSpinFiberMeasure L.rationalQuadraticSpaceMatrix hsurj
      (positiveRationalIdeleToIdeleClassHom a),
    (D.measurable_verticalSpinFiberMeasure L hn hsurj).comp
      measurable_positiveRationalIdeleToIdeleClassHom⟩

/-- Bind the vertical Spin fibers against differential Haar on the exact
positive-idele fundamental domain. -/
noncomputable def positiveDifferentialVerticalSpinFiberBoundMeasure
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass) :
    Measure
      L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinLeftQuotient :=
  Measure.bind
    (positiveRationalIdeleDifferentialHaarMeasure.restrict
      positiveRationalIdeleMeasurableFundamentalDomainSubtype)
    (D.verticalSpinFiberKernelAtPositiveIdele L hn hsurj)

/-- The differential positive-idele bind of a measurable set is the literal
integral of the descended translated Spin fibers. -/
theorem positiveDifferentialVerticalSpinFiberBoundMeasure_apply
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    {s : Set
      L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinLeftQuotient}
    (hs : MeasurableSet s) :
    D.positiveDifferentialVerticalSpinFiberBoundMeasure L hn hsurj s =
      ∫⁻ a : positiveRationalAdeleUnitsSubgroup,
        D.verticalSpinFiberMeasure L.rationalQuadraticSpaceMatrix hsurj
          (positiveRationalIdeleToIdeleClassHom a) s
        ∂(positiveRationalIdeleDifferentialHaarMeasure.restrict
          positiveRationalIdeleMeasurableFundamentalDomainSubtype) := by
  rw [positiveDifferentialVerticalSpinFiberBoundMeasure,
    Measure.bind_apply hs
      (D.verticalSpinFiberKernelAtPositiveIdele L hn hsurj).aemeasurable]
  rfl

/-- Exact outer Weil comparison.  The only coefficient is the independently
certified class-Haar-to-differential-Weil scalar. -/
theorem verticalSpinFiberHaarBoundMeasure_eq_smul_positiveDifferential
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass) :
    D.verticalSpinFiberHaarBoundMeasure L hn hsurj =
      (rationalIdeleClassHaarToDifferentialWeilScalar : ℝ≥0∞) •
        D.positiveDifferentialVerticalSpinFiberBoundMeasure L hn hsurj := by
  ext s hs
  rw [D.verticalSpinFiberHaarBoundMeasure_apply L hn hsurj hs,
    rationalIdeleClassHaarMeasure_eq_smul_differentialWeilQuotient,
    lintegral_smul_measure,
    ← map_positiveRationalIdeleDifferentialHaar_restrict_fundamentalDomain]
  let F : RationalIdeleClassGroup → ℝ≥0∞ := fun c =>
    D.verticalSpinFiberMeasure L.rationalQuadraticSpaceMatrix hsurj c s
  have hF : Measurable F :=
    (D.verticalSpinFiberKernelAtIdeleClass L hn hsurj).measurable_coe hs
  rw [lintegral_map' hF.aemeasurable
    measurable_positiveRationalIdeleToIdeleClassHom.aemeasurable]
  rw [Measure.smul_apply,
    D.positiveDifferentialVerticalSpinFiberBoundMeasure_apply L hn hsurj hs]
  rfl

/-- Exact positive-idele/Spin Tonelli form of the periodized vertical bind.
The outer class-Haar conversion is explicit; the inner measure is still the
literal raw Spin quotient, ready for the specialized Spin Weil step. -/
theorem lintegral_periodizedVerticalSpinFiberHaarBoundMeasure_eq_positiveWeil
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    (f :
      L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup → ℝ≥0∞)
    (hf : Measurable f) :
    let V := L.rationalQuadraticSpaceMatrix
    ∫⁻ x, f x
        ∂V.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift
          (D.verticalSpinFiberHaarBoundMeasure L hn hsurj) =
      (rationalIdeleClassHaarToDifferentialWeilScalar : ℝ≥0∞) *
        ∫⁻ a : positiveRationalAdeleUnitsSubgroup,
          ∫⁻ q : V.FullAdelicCliffordSpinCandidateLeftQuotient,
            leftPeriodize
              V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup f
              (V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul
                (V.verticalGeneralSpinRepresentative hsurj
                  (positiveRationalIdeleToIdeleClassHom a))
                (V.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin q))
            ∂D.spinData.quotientMeasure
          ∂(positiveRationalIdeleDifferentialHaarMeasure.restrict
            positiveRationalIdeleMeasurableFundamentalDomainSubtype) := by
  let V := L.rationalQuadraticSpaceMatrix
  let F := leftPeriodize
    V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup f
  have hF : Measurable F :=
    V.measurable_fullAdelicCliffordGeneralSpinLeftPeriodize f hf
  dsimp only [V]
  rw [V.lintegral_fullAdelicCliffordGeneralSpinPeriodizedQuotientLift_eq_leftPeriodize
    (D.verticalSpinFiberHaarBoundMeasure L hn hsurj) f hf]
  rw [D.verticalSpinFiberHaarBoundMeasure_eq_smul_positiveDifferential
    L hn hsurj, lintegral_smul_measure]
  rw [positiveDifferentialVerticalSpinFiberBoundMeasure,
    Measure.lintegral_bind
      (D.verticalSpinFiberKernelAtPositiveIdele L hn hsurj).aemeasurable
      hF.aemeasurable]
  congr 1
  apply lintegral_congr
  intro a
  change
    (∫⁻ z, F z
      ∂D.verticalSpinFiberMeasure V hsurj
        (positiveRationalIdeleToIdeleClassHom a)) = _
  rw [verticalSpinFiberMeasure]
  rw [lintegral_map hF
    (V.measurable_fullAdelicCliffordGeneralSpinLeftQuotientRightMul
      (V.verticalGeneralSpinRepresentative hsurj
        (positiveRationalIdeleToIdeleClassHom a)))]
  rw [spinGeneralSpinQuotientPushforwardMeasure,
    fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpinPushforward]
  exact lintegral_map'
    (hF.comp
      (V.measurable_fullAdelicCliffordGeneralSpinLeftQuotientRightMul
        (V.verticalGeneralSpinRepresentative hsurj
          (positiveRationalIdeleToIdeleClassHom a)))).aemeasurable
    V.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin_measurable.aemeasurable

end RationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData
