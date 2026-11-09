import SMSFormula.RationalCliffordGeneralSpinVerticalFiberQuotientProper
import SMSFormula.RationalCliffordGeneralSpinHorizontalAdelicUnimodular
import SMSFormula.HaarMeasureUnimodularInversion

/-!
# Haar scale of the vertical Spin-fiber periodization

The exact vertical class-Haar bind has a nonzero, sigma-finite and right
invariant ambient periodization.  Right-Haar uniqueness therefore supplies a
positive finite comparison scalar against inverse fixed horizontal
Haar.  Adelic `GSpin` unimodularity removes the inverse.

The scalar is named.  It is not shown to be one and is not
identified with the horizontal periodization scalar.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open MeasureTheory
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData

variable {n : ℕ}

/-- Right-Haar uniqueness for the periodized vertical bind, before choosing
its positive finite scalar. -/
theorem exists_periodizedVerticalSpinFiberHaarBoundMeasure_eq_smul_inv_horizontal
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift
          (D.verticalSpinFiberHaarBoundMeasure L hn hsurj) =
        c • L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure.inv := by
  let V := L.rationalQuadraticSpaceMatrix
  let μ := V.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift
    (D.verticalSpinFiberHaarBoundMeasure L hn hsurj)
  letI : SecondCountableTopology V.FullAdelicCliffordGeneralSpinGroup :=
    V.fullAdelicCliffordGeneralSpinGroupSecondCountableTopology
  letI : SigmaFinite μ :=
    D.periodizedVerticalSpinFiberHaarBoundMeasure_sigmaFinite L hn hsurj
  letI : Measure.IsMulRightInvariant μ := ⟨fun x =>
    D.map_periodizedVerticalSpinFiberHaarBoundMeasure_rightMul L hn hsurj x⟩
  letI : Measure.IsHaarMeasure
      V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure :=
    V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure_isHaarMeasure
  exact Measure.eq_smul_inv_of_sigmaFinite_rightInvariant
    μ V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure
    (D.periodizedVerticalSpinFiberHaarBoundMeasure_ne_zero L hn hsurj)

/-- The positive finite ambient right-Haar scalar induced by the vertical
Spin disintegration. -/
noncomputable def periodizedVerticalSpinFiberHaarBoundRightHaarScalar
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass) :
    ℝ≥0∞ :=
  Classical.choose
    (D.exists_periodizedVerticalSpinFiberHaarBoundMeasure_eq_smul_inv_horizontal
      L hn hsurj)

theorem periodizedVerticalSpinFiberHaarBoundRightHaarScalar_ne_zero
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass) :
    D.periodizedVerticalSpinFiberHaarBoundRightHaarScalar L hn hsurj ≠ 0 :=
  (Classical.choose_spec
    (D.exists_periodizedVerticalSpinFiberHaarBoundMeasure_eq_smul_inv_horizontal
      L hn hsurj)).1

theorem periodizedVerticalSpinFiberHaarBoundRightHaarScalar_ne_top
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass) :
    D.periodizedVerticalSpinFiberHaarBoundRightHaarScalar L hn hsurj ≠ ∞ :=
  (Classical.choose_spec
    (D.exists_periodizedVerticalSpinFiberHaarBoundMeasure_eq_smul_inv_horizontal
      L hn hsurj)).2.1

/-- Exact right-Haar comparison retaining the inverse reference measure. -/
theorem periodizedVerticalSpinFiberHaarBoundMeasure_eq_smul_inv_horizontal
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass) :
    L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift
        (D.verticalSpinFiberHaarBoundMeasure L hn hsurj) =
      D.periodizedVerticalSpinFiberHaarBoundRightHaarScalar L hn hsurj •
        L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure.inv :=
  (Classical.choose_spec
    (D.exists_periodizedVerticalSpinFiberHaarBoundMeasure_eq_smul_inv_horizontal
      L hn hsurj)).2.2

/-- Exact ambient Haar comparison after consuming adelic `GSpin`
unimodularity.  The vertical scalar remains explicit. -/
theorem periodizedVerticalSpinFiberHaarBoundMeasure_eq_smul_horizontal
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass) :
    L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift
        (D.verticalSpinFiberHaarBoundMeasure L hn hsurj) =
      D.periodizedVerticalSpinFiberHaarBoundRightHaarScalar L hn hsurj •
        L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure := by
  rw [D.periodizedVerticalSpinFiberHaarBoundMeasure_eq_smul_inv_horizontal
      L hn hsurj,
    L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure_inv]

/-- Restriction to the exact rational `GSpin` fundamental domain recovers the
vertical class-Haar bind as the same explicit scalar multiple of the certified
common horizontal quotient. -/
theorem verticalSpinFiberHaarBoundMeasure_eq_smul_horizontalQuotientMeasure
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass) :
    D.verticalSpinFiberHaarBoundMeasure L hn hsurj =
      D.periodizedVerticalSpinFiberHaarBoundRightHaarScalar L hn hsurj •
        L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinHorizontalMeasurableWeilData.quotientMeasure := by
  let V := L.rationalQuadraticSpaceMatrix
  let μ := D.verticalSpinFiberHaarBoundMeasure L hn hsurj
  let c := D.periodizedVerticalSpinFiberHaarBoundRightHaarScalar L hn hsurj
  let F := V.fullAdelicCliffordGeneralSpinMeasurableFundamentalDomain
  have hperiodized :=
    D.periodizedVerticalSpinFiberHaarBoundMeasure_eq_smul_horizontal L hn hsurj
  have hrestrict :
      (V.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift μ).restrict F =
        (c • V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure).restrict F := by
    simpa only [V, μ, c, F] using congrArg
      (fun ρ : Measure V.FullAdelicCliffordGeneralSpinGroup => ρ.restrict F)
      hperiodized
  rw [V.restrict_fullAdelicCliffordGeneralSpinPeriodizedQuotientLift μ,
    Measure.restrict_smul] at hrestrict
  have hmap := congrArg
    (Measure.map V.fullAdelicCliffordGeneralSpinLeftQuotientMap) hrestrict
  rw [V.map_fullAdelicCliffordGeneralSpinLeftQuotientMap_fundamentalSectionLift μ,
    Measure.map_smul] at hmap
  rw [V.fullAdelicCliffordGeneralSpinHorizontalMeasurableWeilData_quotientMeasure_eq_fundamentalDomain]
  simpa only [V, μ, c, leftQuotientFundamentalDomainMeasure_eq_map_restrict] using hmap

end RationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData
