import SMSFormula.HaarMeasureUnimodularInversion
import SMSFormula.RationalCliffordGeneralSpinAdelicQuotientMeasurePeriodizedSigmaFinite
import SMSFormula.RationalCliffordGeneralSpinHorizontalQuotientMeasure

/-!
# The periodized horizontal GSpin bind is a right Haar measure

The concrete raw-`SO`/idele-class quotient bind is nonzero, sigma-finite and
right invariant after periodization.  General right-Haar uniqueness therefore
compares it with a positive finite scalar multiple of the inverse of the fixed
horizontal adelic left Haar measure.

The inverse is essential.  Replacing it by the horizontal measure itself
would assert adelic `GSpin` unimodularity, which is not proved here and belongs
to the remaining central-extension differential calculation.
-/

noncomputable section

open MeasureTheory
open RationalQuadraticSpaceMatrix
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

/-- The concrete periodized ambient lift is nonzero. -/
theorem periodizedHorizontalRawSOFiberHaarBoundMeasure_ne_zero
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hn : 3 ≤ r + 2)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P) :
    L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift
        (L.horizontalRawSOFiberHaarBoundMeasure inst
          (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
            L hn inst hP hconv)) ≠ 0 := by
  exact
    L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift_ne_zero
      (L.horizontalRawSOFiberHaarBoundMeasure inst
        (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
          L hn inst hP hconv))
      (L.horizontalRawSOFiberHaarBoundMeasure_ne_zero hn inst hP hconv)

/-- Right-Haar uniqueness for the concrete periodized lift, stated before
choosing its proportionality scalar. -/
theorem exists_periodizedHorizontalRawSOFiberHaarBoundMeasure_eq_smul_inv_horizontal
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hn : 3 ≤ r + 2)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift
          (L.horizontalRawSOFiberHaarBoundMeasure inst
            (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
              L hn inst hP hconv)) =
        c • L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure.inv := by
  let V := L.rationalQuadraticSpaceMatrix
  let μ := V.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift
    (L.horizontalRawSOFiberHaarBoundMeasure inst
      (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
        L hn inst hP hconv))
  letI : SecondCountableTopology V.FullAdelicCliffordGeneralSpinGroup :=
    V.fullAdelicCliffordGeneralSpinGroupSecondCountableTopology
  letI : SigmaFinite μ :=
    L.periodizedHorizontalRawSOFiberHaarBoundMeasure_sigmaFinite
      hn inst hP hconv
  letI : Measure.IsMulRightInvariant μ := ⟨fun x =>
    L.map_periodizedHorizontalRawSOFiberHaarBoundMeasure_rightMul
      hn inst hP hconv x⟩
  letI : Measure.IsHaarMeasure
      V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure :=
    V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure_isHaarMeasure
  exact Measure.eq_smul_inv_of_sigmaFinite_rightInvariant
    μ V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure
    (L.periodizedHorizontalRawSOFiberHaarBoundMeasure_ne_zero
      hn inst hP hconv)

/-- The positive finite right-Haar scalar of the concrete ambient
periodization relative to inverse horizontal Haar. -/
noncomputable def periodizedHorizontalRawSOFiberHaarBoundRightHaarScalar
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hn : 3 ≤ r + 2)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P) : ℝ≥0∞ :=
  Classical.choose
    (L.exists_periodizedHorizontalRawSOFiberHaarBoundMeasure_eq_smul_inv_horizontal
      hn inst hP hconv)

theorem periodizedHorizontalRawSOFiberHaarBoundRightHaarScalar_ne_zero
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hn : 3 ≤ r + 2)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P) :
    L.periodizedHorizontalRawSOFiberHaarBoundRightHaarScalar
        hn inst hP hconv ≠ 0 :=
  (Classical.choose_spec
    (L.exists_periodizedHorizontalRawSOFiberHaarBoundMeasure_eq_smul_inv_horizontal
      hn inst hP hconv)).1

theorem periodizedHorizontalRawSOFiberHaarBoundRightHaarScalar_ne_top
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hn : 3 ≤ r + 2)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P) :
    L.periodizedHorizontalRawSOFiberHaarBoundRightHaarScalar
        hn inst hP hconv ≠ ∞ :=
  (Classical.choose_spec
    (L.exists_periodizedHorizontalRawSOFiberHaarBoundMeasure_eq_smul_inv_horizontal
      hn inst hP hconv)).2.1

/-- Exact concrete right-Haar comparison.  The target remains inverse
horizontal Haar until unimodularity is certified. -/
theorem periodizedHorizontalRawSOFiberHaarBoundMeasure_eq_smul_inv_horizontal
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hn : 3 ≤ r + 2)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P) :
    L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift
        (L.horizontalRawSOFiberHaarBoundMeasure inst
          (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
            L hn inst hP hconv)) =
      L.periodizedHorizontalRawSOFiberHaarBoundRightHaarScalar
          hn inst hP hconv •
        L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure.inv :=
  (Classical.choose_spec
    (L.exists_periodizedHorizontalRawSOFiberHaarBoundMeasure_eq_smul_inv_horizontal
      hn inst hP hconv)).2.2

/-- The concrete periodized lift is locally finite. -/
theorem periodizedHorizontalRawSOFiberHaarBoundMeasure_isFiniteMeasureOnCompacts
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hn : 3 ≤ r + 2)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P) :
    IsFiniteMeasureOnCompacts
      (L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift
        (L.horizontalRawSOFiberHaarBoundMeasure inst
          (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
            L hn inst hP hconv))) := by
  let V := L.rationalQuadraticSpaceMatrix
  let c := L.periodizedHorizontalRawSOFiberHaarBoundRightHaarScalar
    hn inst hP hconv
  rw [L.periodizedHorizontalRawSOFiberHaarBoundMeasure_eq_smul_inv_horizontal
    hn inst hP hconv]
  letI : Measure.IsHaarMeasure
      V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure :=
    V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure_isHaarMeasure
  letI : IsFiniteMeasureOnCompacts
      V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure.inv := by
    infer_instance
  exact IsFiniteMeasureOnCompacts.smul _
    (L.periodizedHorizontalRawSOFiberHaarBoundRightHaarScalar_ne_top
      hn inst hP hconv)

/-- Every nonempty open set has positive mass in the concrete periodized
lift. -/
theorem periodizedHorizontalRawSOFiberHaarBoundMeasure_isOpenPosMeasure
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hn : 3 ≤ r + 2)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P) :
    Measure.IsOpenPosMeasure
      (L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift
        (L.horizontalRawSOFiberHaarBoundMeasure inst
          (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
            L hn inst hP hconv))) := by
  let V := L.rationalQuadraticSpaceMatrix
  rw [L.periodizedHorizontalRawSOFiberHaarBoundMeasure_eq_smul_inv_horizontal
    hn inst hP hconv]
  letI : Measure.IsHaarMeasure
      V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure :=
    V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure_isHaarMeasure
  letI : Measure.IsOpenPosMeasure
      V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure.inv := by
    infer_instance
  exact Measure.isOpenPosMeasure_smul _
    (L.periodizedHorizontalRawSOFiberHaarBoundRightHaarScalar_ne_zero
      hn inst hP hconv)

end PositiveDefiniteIntegralLattice
