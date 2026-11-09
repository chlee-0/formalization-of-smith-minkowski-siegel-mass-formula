import SMSFormula.RationalCliffordGeneralSpinRawHorizontalCrossedCutoff
import SMSFormula.RationalCliffordGeneralSpinRawVerticalCrossedCutoff
import SMSFormula.RationalIdeleClassHaarDilation
import SMSFormula.RationalCliffordSpinCandidateRawQuotientVolumePositive
import SMSFormula.RationalCliffordSpinCandidateLatticeRawOnoTamagawaData
import SMSFormula.RationalCliffordGeneralSpinLatticeFullAdelicSOSurjectivity
import SMSFormula.SpecialOrthogonalAdelicDifferentialNormalizationCertificate

/-!
# Extracting the Spin--SO ratio from one crossed cutoff

The two actual crossed iterated integrals have already been evaluated in
terms of the raw Spin and `SO` quotient masses.  This file isolates the final
analytic cancellation: equality of those two integrals for one nonzero
finite logarithmic cutoff, together with the literal idele-class squaring
Jacobian, forces the relative factor two.

The common-integral equality remains a concrete measure statement about the
implemented `GSpin` quotient.  It is not replaced by an applicability
predicate or by the desired numerical conclusion.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

local instance crossedCutoffMultiplicativeMeasureSpace :
    MeasureSpace (Multiplicative ℝ) :=
  inferInstanceAs (MeasureSpace ℝ)

local instance crossedCutoffMultiplicativeBorelSpace :
    BorelSpace (Multiplicative ℝ) := by
  change BorelSpace ℝ
  infer_instance

local instance crossedCutoffMultiplicativeVolumeIsHaarMeasure :
    Measure.IsHaarMeasure (volume : Measure (Multiplicative ℝ)) := by
  letI : IsFiniteMeasureOnCompacts (volume : Measure (Multiplicative ℝ)) :=
    inferInstanceAs (IsFiniteMeasureOnCompacts (volume : Measure ℝ))
  letI : Measure.IsOpenPosMeasure (volume : Measure (Multiplicative ℝ)) :=
    inferInstanceAs (Measure.IsOpenPosMeasure (volume : Measure ℝ))
  refine
    { toIsMulLeftInvariant := ?_
      lt_top_of_isCompact := fun K hK => hK.measure_lt_top
      toIsOpenPosMeasure := inferInstance }
  constructor
  intro g
  change Measure.map (fun x : ℝ => g.toAdd + x) volume = volume
  exact MeasureTheory.map_add_left_eq_self volume g.toAdd

/-- The fixed compactly supported cutoff used to extract the crossed ratio. -/
def rationalIdeleClassUnitLogCutoff (t : ℝ) : ℝ≥0∞ :=
  Set.indicator (Set.Ioc (0 : ℝ) 1) (fun _ => 1) t

theorem measurable_rationalIdeleClassUnitLogCutoff :
    Measurable rationalIdeleClassUnitLogCutoff := by
  exact measurable_const.indicator measurableSet_Ioc

theorem lintegral_rationalIdeleClassUnitLogCutoff :
    (∫⁻ t : ℝ, rationalIdeleClassUnitLogCutoff t) = 1 := by
  rw [show rationalIdeleClassUnitLogCutoff =
      Set.indicator (Set.Ioc (0 : ℝ) 1) (fun _ : ℝ => (1 : ℝ≥0∞)) by rfl]
  rw [lintegral_indicator measurableSet_Ioc]
  simp

theorem rationalIdeleClassLogHaarScalar_pos :
    0 < rationalIdeleClassLogHaarScalar := by
  letI : Measure.IsHaarMeasure
      (Measure.map rationalIdeleClassLogModuleHom rationalIdeleClassHaarMeasure) :=
    rationalIdeleClassLogModulePushforwardIsHaarMeasure
  unfold rationalIdeleClassLogHaarScalar
  exact_mod_cast Measure.haarScalarFactor_pos_of_isHaarMeasure
    (Measure.map rationalIdeleClassLogModuleHom
      rationalIdeleClassHaarMeasure)
    (volume : Measure (Multiplicative ℝ))

theorem rationalIdeleClassLogHaarScalar_ne_top :
    rationalIdeleClassLogHaarScalar ≠ ⊤ := by
  unfold rationalIdeleClassLogHaarScalar
  exact ENNReal.coe_ne_top

theorem rationalIdeleClassLogCutoffLIntegral_unit_ne_zero :
    rationalIdeleClassLogCutoffLIntegral
        rationalIdeleClassUnitLogCutoff ≠ 0 := by
  rw [rationalIdeleClassLogCutoffLIntegral_eq_real
    rationalIdeleClassUnitLogCutoff
    measurable_rationalIdeleClassUnitLogCutoff,
    lintegral_rationalIdeleClassUnitLogCutoff, mul_one]
  exact rationalIdeleClassLogHaarScalar_pos.ne'

theorem rationalIdeleClassLogCutoffLIntegral_unit_ne_top :
    rationalIdeleClassLogCutoffLIntegral
        rationalIdeleClassUnitLogCutoff ≠ ⊤ := by
  rw [rationalIdeleClassLogCutoffLIntegral_eq_real
    rationalIdeleClassUnitLogCutoff
    measurable_rationalIdeleClassUnitLogCutoff,
    lintegral_rationalIdeleClassUnitLogCutoff, mul_one]
  exact rationalIdeleClassLogHaarScalar_ne_top

namespace CliffordSpinCandidateRawOnoTamagawaData

variable {n : ℕ} {V : RationalQuadraticSpaceMatrix n}

/-- Equality of the two actual crossed iterated integrals for the fixed unit
cutoff forces the raw Spin--`SO` relative Tamagawa comparison, provided the
raw `SO` quotient mass is finite. -/
theorem isOnoRelativeTamagawaComparison_of_unitCrossedCutoff_eq
    (D : V.CliffordSpinCandidateRawOnoTamagawaData)
    (hHorizontal : Function.Surjective
      V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal)
    (hVertical : Function.Surjective
      V.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    (hSOtop : D.specialOrthogonalData.tamagawaNumberENNReal ≠ ⊤)
    (hcrossed :
      D.horizontalCrossedLogCutoffLIntegral V hHorizontal
          rationalIdeleClassUnitLogCutoff =
        D.verticalCrossedLogCutoffLIntegral V hVertical
          rationalIdeleClassUnitLogCutoff) :
    D.IsOnoRelativeTamagawaComparison := by
  let C := rationalIdeleClassLogCutoffLIntegral
    rationalIdeleClassUnitLogCutoff
  have hC0 : C ≠ 0 :=
    rationalIdeleClassLogCutoffLIntegral_unit_ne_zero
  have hCtop : C ≠ ⊤ :=
    rationalIdeleClassLogCutoffLIntegral_unit_ne_top
  have hcrossed' :
      (2 : ℝ≥0∞)⁻¹ * C *
          D.specialOrthogonalData.tamagawaNumberENNReal =
        C * D.spinTamagawaNumberENNReal := by
    rw [D.horizontalCrossedLogCutoffLIntegral_eq V hHorizontal
        rationalIdeleClassUnitLogCutoff
        measurable_rationalIdeleClassUnitLogCutoff,
      V.horizontalFiberLogCutoffLIntegral_one
        rationalIdeleClassUnitLogCutoff
        measurable_rationalIdeleClassUnitLogCutoff,
      D.verticalCrossedLogCutoffLIntegral_eq V hVertical
        rationalIdeleClassUnitLogCutoff
        measurable_rationalIdeleClassUnitLogCutoff] at hcrossed
    change rationalIdeleClassLogCutoffLIntegral
        (fun t => rationalIdeleClassUnitLogCutoff (2 * t)) *
          D.specialOrthogonalData.tamagawaNumberENNReal =
        C * D.spinTamagawaNumberENNReal at hcrossed
    rw [rationalIdeleClassLogCutoffLIntegral_two_mul
      rationalIdeleClassUnitLogCutoff
      measurable_rationalIdeleClassUnitLogCutoff] at hcrossed
    exact hcrossed
  have hhalf :
      (2 : ℝ≥0∞)⁻¹ *
          D.specialOrthogonalData.tamagawaNumberENNReal =
        D.spinTamagawaNumberENNReal := by
    let a := (2 : ℝ≥0∞)⁻¹ *
      D.specialOrthogonalData.tamagawaNumberENNReal
    have hCa : C * a = C * D.spinTamagawaNumberENNReal := by
      change C * ((2 : ℝ≥0∞)⁻¹ *
          D.specialOrthogonalData.tamagawaNumberENNReal) = _
      rw [← hcrossed']
      ac_rfl
    change a = D.spinTamagawaNumberENNReal
    calc
      a = 1 * a := by rw [one_mul]
      _ = (C⁻¹ * C) * a := by
        rw [ENNReal.inv_mul_cancel hC0 hCtop]
      _ = C⁻¹ * (C * a) := by ac_rfl
      _ = C⁻¹ * (C * D.spinTamagawaNumberENNReal) := by rw [hCa]
      _ = (C⁻¹ * C) * D.spinTamagawaNumberENNReal := by ac_rfl
      _ = D.spinTamagawaNumberENNReal := by
        rw [ENNReal.inv_mul_cancel hC0 hCtop, one_mul]
  have hspinTop : D.spinTamagawaNumberENNReal ≠ ⊤ := by
    rw [← hhalf]
    exact ENNReal.mul_ne_top (by simp) hSOtop
  have hSO :
      D.specialOrthogonalData.tamagawaNumberENNReal =
        2 * D.spinTamagawaNumberENNReal := by
    calc
      D.specialOrthogonalData.tamagawaNumberENNReal =
          2 * ((2 : ℝ≥0∞)⁻¹ *
            D.specialOrthogonalData.tamagawaNumberENNReal) := by
        rw [← mul_assoc,
          ENNReal.mul_inv_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
            (by norm_num : (2 : ℝ≥0∞) ≠ ⊤), one_mul]
      _ = 2 * D.spinTamagawaNumberENNReal := by rw [hhalf]
  rw [D.isOnoRelativeTamagawaComparison_iff, hSO]
  rw [mul_div_assoc,
    ENNReal.div_self D.spinTamagawaNumberENNReal_ne_zero hspinTop, mul_one]

end CliffordSpinCandidateRawOnoTamagawaData

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The horizontal adelic `GSpin -> SO` quotient map is surjective in every
lattice rank at least three, without exposing the internal `r + 2`
parameter. -/
theorem fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal_surjective_of_rankAtLeastThree
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n) :
    Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal := by
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 2 := ⟨n - 2, by omega⟩
  exact fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal_surjective L

/-- The vertical adelic `GSpin` quotient fills the idele-class base in every
lattice rank at least three. -/
theorem fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass_surjective_of_rankAtLeastThree
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n) :
    Function.Surjective
      (RationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass
        L.rationalQuadraticSpaceMatrix) := by
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 2 := ⟨n - 2, by omega⟩
  exact fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass_surjective L
    (by omega)

/-- For the exact lattice raw datum, the only remaining relative-comparison
input is equality of the two literal crossed integrals for the fixed compact
cutoff. The raw `SO` finiteness needed for cancellation comes from the
existing differential normalization certificate. -/
theorem
    cliffordSpinCandidateRawOnoTamagawaDataOfLattice_isOnoRelativeComparison_of_unitCrossedCutoff_eq
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)] (hn : 3 ≤ n)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P)
    (hcrossed :
      let V := L.rationalQuadraticSpaceMatrix
      let D := cliffordSpinCandidateRawOnoTamagawaDataOfLattice
        L hn inst hP hconv
      D.horizontalCrossedLogCutoffLIntegral V
          (L.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal_surjective_of_rankAtLeastThree
            hn)
          RationalQuadraticSpaceMatrix.rationalIdeleClassUnitLogCutoff =
        D.verticalCrossedLogCutoffLIntegral V
          (L.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass_surjective_of_rankAtLeastThree
            hn)
          RationalQuadraticSpaceMatrix.rationalIdeleClassUnitLogCutoff) :
    (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
      L hn inst hP hconv).IsOnoRelativeTamagawaComparison := by
  let V := L.rationalQuadraticSpaceMatrix
  let D := cliffordSpinCandidateRawOnoTamagawaDataOfLattice
    L hn inst hP hconv
  let hHorizontal :=
    L.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal_surjective_of_rankAtLeastThree
      hn
  let hVertical :=
    L.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass_surjective_of_rankAtLeastThree
      hn
  have hcertificate :=
    RationalQuadraticSpaceMatrixFullAdelicDifferentialNormalizationCertificate.of_massLocalInverseProductTendsTo
      L inst hP hconv
  have hSOtop : D.specialOrthogonalData.tamagawaNumberENNReal ≠ ⊤ := by
    change
      (L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasurableWeilMeasureData
        inst hP).tamagawaNumberENNReal ≠ ⊤
    exact hcertificate.tamagawaNumberENNReal_ne_top
  exact
    D.isOnoRelativeTamagawaComparison_of_unitCrossedCutoff_eq
      hHorizontal hVertical hSOtop hcrossed

end PositiveDefiniteIntegralLattice
