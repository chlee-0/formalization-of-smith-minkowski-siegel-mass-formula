import SMSFormula.RationalCliffordGeneralSpinAdelicQuotientMeasurePeriodizedLift
import SMSFormula.RationalCliffordGeneralSpinHorizontalBoundRightTranslation

/-!
# Right invariance of periodized adelic GSpin quotient measures

The rational-diagonal sum defining the ambient periodized lift is the
integral of the ordinary left periodization on the quotient.  Right
multiplication commutes with that left periodization after passing to the
quotient.  Consequently every right-invariant quotient measure has a
right-invariant ambient periodized lift.

The final theorem specializes this general statement to the concrete raw
`SO`/idele-class horizontal bind.  No sigma-finiteness, Haar proportionality,
or normalization scalar is asserted here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open MeasureTheory
open Set
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-- The rational-diagonal periodization of a measurable nonnegative ambient
function is measurable on the actual rational adelic GSpin quotient. -/
theorem measurable_fullAdelicCliffordGeneralSpinLeftPeriodize
    (f : V.FullAdelicCliffordGeneralSpinGroup → ℝ≥0∞)
    (hf : Measurable f) :
    Measurable
      (leftPeriodize
        V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup f) := by
  letI : Countable
      V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup :=
    V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup_countable
  exact leftPeriodize_measurable_map_of_leftPreperiodize
    V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup
    (leftPreperiodize_measurable_of_countable
      V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup hf)

/-- The ambient periodized-lift integral is the quotient integral of the
ordinary rational-diagonal left periodization. -/
theorem lintegral_fullAdelicCliffordGeneralSpinPeriodizedQuotientLift_eq_leftPeriodize
    (μ : Measure V.FullAdelicCliffordGeneralSpinLeftQuotient)
    (f : V.FullAdelicCliffordGeneralSpinGroup → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ x, f x ∂V.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift μ =
      ∫⁻ y,
        leftPeriodize
          V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup f y ∂μ := by
  letI : Countable
      V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup :=
    V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup_countable
  rw [V.lintegral_fullAdelicCliffordGeneralSpinPeriodizedQuotientLift μ f hf]
  have hterm :
      ∀ gamma : V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup,
        AEMeasurable
          (fun y : V.FullAdelicCliffordGeneralSpinLeftQuotient =>
            f (V.fullAdelicCliffordGeneralSpinRationalTranslateFundamentalSection
              gamma y)) μ := by
    intro gamma
    exact (hf.comp
      (V.measurable_fullAdelicCliffordGeneralSpinRationalTranslateFundamentalSection
        gamma)).aemeasurable
  rw [← lintegral_tsum hterm]
  apply lintegral_congr
  intro y
  change
    leftPreperiodize
        V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup f
        (V.fullAdelicCliffordGeneralSpinFundamentalDomainSection y) =
      leftPeriodize
        V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup f y
  calc
    leftPreperiodize
        V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup f
        (V.fullAdelicCliffordGeneralSpinFundamentalDomainSection y) =
      leftPeriodize
        V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup f
        (leftCosetMap
          V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup
          (V.fullAdelicCliffordGeneralSpinFundamentalDomainSection y)) :=
        (leftPeriodize_leftCosetMap
          V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup f
          (V.fullAdelicCliffordGeneralSpinFundamentalDomainSection y)).symm
    _ = leftPeriodize
        V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup f y := by
      rw [show
        leftCosetMap V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup
            (V.fullAdelicCliffordGeneralSpinFundamentalDomainSection y) = y from
          V.fullAdelicCliffordGeneralSpinLeftQuotientMap_fundamentalDomainSection y]

/-- Right multiplication of the ambient integrand is the same as right
multiplication of its descended left periodization on the quotient. -/
theorem fullAdelicCliffordGeneralSpinLeftPeriodize_rightMul
    (f : V.FullAdelicCliffordGeneralSpinGroup → ℝ≥0∞)
    (x : V.FullAdelicCliffordGeneralSpinGroup)
    (y : V.FullAdelicCliffordGeneralSpinLeftQuotient) :
    leftPeriodize
        V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup
        (fun z => f (z * x)) y =
      leftPeriodize
        V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup f
        (V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul x y) := by
  induction y using Quot.inductionOn with
  | _ y =>
    change (∑' gamma :
        V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup,
          f (((gamma : V.FullAdelicCliffordGeneralSpinGroup) * y) * x)) =
      ∑' gamma : V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup,
        f ((gamma : V.FullAdelicCliffordGeneralSpinGroup) * (y * x))
    apply tsum_congr
    intro gamma
    rw [mul_assoc]

/-- Periodization transports quotient right invariance to genuine ambient
right invariance. -/
theorem map_fullAdelicCliffordGeneralSpinPeriodizedQuotientLift_rightMul_of_map_eq
    (μ : Measure V.FullAdelicCliffordGeneralSpinLeftQuotient)
    (x : V.FullAdelicCliffordGeneralSpinGroup)
    (hμ : Measure.map
        (V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul x) μ = μ) :
    Measure.map (fun z : V.FullAdelicCliffordGeneralSpinGroup => z * x)
        (V.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift μ) =
      V.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift μ := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (measurable_mul_const x)]
  rw [V.lintegral_fullAdelicCliffordGeneralSpinPeriodizedQuotientLift_eq_leftPeriodize
    μ (fun z => f (z * x)) (hf.comp (measurable_mul_const x))]
  rw [V.lintegral_fullAdelicCliffordGeneralSpinPeriodizedQuotientLift_eq_leftPeriodize
    μ f hf]
  have hperiodize : Measurable
      (leftPeriodize
        V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup f) :=
    V.measurable_fullAdelicCliffordGeneralSpinLeftPeriodize f hf
  calc
    ∫⁻ y,
        leftPeriodize
          V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup
          (fun z => f (z * x)) y ∂μ =
      ∫⁻ y,
        leftPeriodize
          V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup f
          (V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul x y) ∂μ := by
        apply lintegral_congr
        exact V.fullAdelicCliffordGeneralSpinLeftPeriodize_rightMul f x
    _ = ∫⁻ y,
        leftPeriodize
          V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup f y
          ∂Measure.map
            (V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul x) μ := by
        rw [lintegral_map hperiodize
          (V.measurable_fullAdelicCliffordGeneralSpinLeftQuotientRightMul x)]
    _ = ∫⁻ y,
        leftPeriodize
          V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup f y ∂μ := by
        rw [hμ]

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

/-- The periodized ambient lift of the literal raw-`SO` horizontal fiber-Haar
bind is invariant under every genuine adelic GSpin right translation. -/
theorem map_periodizedHorizontalRawSOFiberHaarBoundMeasure_rightMul
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hn : 3 ≤ r + 2)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P)
    (x : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup) :
    Measure.map
        (fun z :
          L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup =>
            z * x)
        (L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift
          (L.horizontalRawSOFiberHaarBoundMeasure inst
            (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
              L hn inst hP hconv))) =
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift
        (L.horizontalRawSOFiberHaarBoundMeasure inst
          (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
            L hn inst hP hconv)) := by
  exact
    L.rationalQuadraticSpaceMatrix.map_fullAdelicCliffordGeneralSpinPeriodizedQuotientLift_rightMul_of_map_eq
      (L.horizontalRawSOFiberHaarBoundMeasure inst
        (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
          L hn inst hP hconv)) x
      (L.map_horizontalRawSOFiberHaarBoundMeasure_rightMul
        hn inst hP hconv x)

end PositiveDefiniteIntegralLattice
