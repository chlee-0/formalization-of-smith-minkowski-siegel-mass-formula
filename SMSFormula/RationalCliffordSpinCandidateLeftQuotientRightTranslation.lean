import SMSFormula.RationalCliffordSpinCandidateCanonicalRightQuotient

/-!
# Right translation of the raw Spin left quotient

Right multiplication by an adelic Spin point descends to the non-normal
rational left quotient.  The actual raw quotient measure is invariant under
this action.  The proof uses only the existing measurable Weil formula and
right invariance of the raw ambient differential measure: translating the
quotient turns the periodization of `f` into the periodization of
`g ↦ f (g * x)`, whose ambient integral is unchanged.  Uniqueness from the
already constructed exact measurable fundamental domain then identifies the
translated quotient measure with the original one.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open MeasureTheory
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} {V : RationalQuadraticSpaceMatrix n}

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1800000

/-- Right multiplication by an adelic Spin point on the rational Spin left
quotient. -/
def fullAdelicCliffordSpinCandidateLeftQuotientRightMul
    (V : RationalQuadraticSpaceMatrix n)
    (x : V.FullAdelicCliffordSpinCandidateGroup) :
    V.FullAdelicCliffordSpinCandidateLeftQuotient →
      V.FullAdelicCliffordSpinCandidateLeftQuotient :=
  Quot.lift
    (fun y => V.fullAdelicCliffordSpinCandidateLeftQuotientMap (y * x)) (by
      intro y z hyz
      rcases hyz with ⟨gamma, rfl⟩
      change V.fullAdelicCliffordSpinCandidateLeftQuotientMap (y * x) =
        V.fullAdelicCliffordSpinCandidateLeftQuotientMap
          (((gamma : V.FullAdelicCliffordSpinCandidateGroup) * y) * x)
      rw [mul_assoc]
      exact (leftCosetMap_gamma_mul
        V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup gamma
        (y * x)).symm)

@[simp]
theorem fullAdelicCliffordSpinCandidateLeftQuotientRightMul_mk
    (V : RationalQuadraticSpaceMatrix n)
    (x y : V.FullAdelicCliffordSpinCandidateGroup) :
    V.fullAdelicCliffordSpinCandidateLeftQuotientRightMul x
        (V.fullAdelicCliffordSpinCandidateLeftQuotientMap y) =
      V.fullAdelicCliffordSpinCandidateLeftQuotientMap (y * x) :=
  rfl

/-- Quotient right multiplication is measurable for the existing
map-generated Spin quotient Borel structure. -/
theorem measurable_fullAdelicCliffordSpinCandidateLeftQuotientRightMul
    (V : RationalQuadraticSpaceMatrix n)
    (x : V.FullAdelicCliffordSpinCandidateGroup) :
    Measurable (V.fullAdelicCliffordSpinCandidateLeftQuotientRightMul x) := by
  rw [measurable_iff_comap_le]
  refine MeasurableSpace.comap_le_iff_le_map.mp ?_
  have hrep : Measurable
      (fun y : V.FullAdelicCliffordSpinCandidateGroup =>
        V.fullAdelicCliffordSpinCandidateLeftQuotientMap (y * x)) :=
    V.fullAdelicCliffordSpinCandidateLeftQuotientMap_measurable.comp
      (continuous_mul_right x).measurable
  simpa [fullAdelicCliffordSpinCandidateLeftQuotientRightMul,
    Function.comp_def] using measurable_iff_comap_le.mp hrep

namespace CliffordSpinCandidateRawOnoTamagawaData

/-- The actual raw Spin left quotient measure is invariant under every
adelic right translation. -/
theorem map_spin_quotientMeasure_rightMul
    (D : V.CliffordSpinCandidateRawOnoTamagawaData)
    (x : V.FullAdelicCliffordSpinCandidateGroup) :
    Measure.map (V.fullAdelicCliffordSpinCandidateLeftQuotientRightMul x)
        D.spinData.quotientMeasure =
      D.spinData.quotientMeasure := by
  letI : Countable V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup :=
    V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup_countable
  letI : Measure.IsInvInvariant D.spinData.adelicMeasure :=
    D.spinRaw.adelicMeasure_isInvInvariant
  letI : Measure.IsHaarMeasure D.spinData.adelicMeasure := by
    rw [D.spinRaw.adelicMeasure_eq]
    exact V.fullAdelicCliffordSpinCandidateRawDifferentialGroupMeasure_isHaarMeasure
      D.spinFiniteScale D.spinRaw.volumeProductCertificate
  letI : Measure.IsMulLeftInvariant D.spinData.adelicMeasure := by
    infer_instance
  letI : Measure.IsMulRightInvariant D.spinData.adelicMeasure :=
    Measure.isMulRightInvariant_of_isInvInvariant D.spinData.adelicMeasure
  let translated := Measure.map
    (V.fullAdelicCliffordSpinCandidateLeftQuotientRightMul x)
    D.spinData.quotientMeasure
  have htranslated : IsLeftMeasurableWeilQuotientMeasure
      V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup
      D.spinData.adelicMeasure translated := by
    constructor
    intro f hf
    have hpre : Measurable
        (leftPreperiodize
          V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup f) :=
      leftPreperiodize_measurable_of_countable
        V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup hf
    have hperiod : Measurable
        (leftPeriodize
          V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup f) := by
      exact leftPeriodize_measurable_map_of_leftPreperiodize
        V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup hpre
    rw [lintegral_map' hperiod.aemeasurable
      (V.measurable_fullAdelicCliffordSpinCandidateLeftQuotientRightMul x).aemeasurable]
    let fx : V.FullAdelicCliffordSpinCandidateGroup → ℝ≥0∞ := fun y => f (y * x)
    have hfx : Measurable fx := hf.comp (continuous_mul_right x).measurable
    have hperiodTranslate :
        (leftPeriodize
            V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup f) ∘
            V.fullAdelicCliffordSpinCandidateLeftQuotientRightMul x =
          leftPeriodize
            V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup fx := by
      funext q
      induction q using Quot.inductionOn with
      | _ y =>
        change leftPreperiodize
            V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup f (y * x) =
          leftPreperiodize
            V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup fx y
        unfold leftPreperiodize fx
        apply tsum_congr
        intro gamma
        simp [mul_assoc]
    change (∫⁻ a,
      ((leftPeriodize
          V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup f) ∘
        V.fullAdelicCliffordSpinCandidateLeftQuotientRightMul x) a
        ∂D.spinData.quotientMeasure) = _
    rw [hperiodTranslate]
    rw [D.spinData.isMeasurableWeilQuotientMeasure.lintegral_leftPeriodize_eq fx hfx]
    calc
      (∫⁻ y, fx y ∂D.spinData.adelicMeasure) =
          ∫⁻ y, f y ∂Measure.map (fun y => y * x) D.spinData.adelicMeasure := by
        rw [lintegral_map' hf.aemeasurable
          (continuous_mul_right x).measurable.aemeasurable]
      _ = ∫⁻ y, f y ∂D.spinData.adelicMeasure := by
        rw [MeasureTheory.map_mul_right_eq_self]
  have htranslatedEq := htranslated.eq_leftQuotientFundamentalDomainMeasure
    V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup rfl
    V.measurableSet_fullAdelicCliffordSpinCandidateMeasurableFundamentalDomain
    V.existsUnique_rationalDiagonal_smul_mem_measurableFundamentalDomain
  have horiginalEq :=
    D.spinData.isMeasurableWeilQuotientMeasure
      |>.eq_leftQuotientFundamentalDomainMeasure
        V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup rfl
        V.measurableSet_fullAdelicCliffordSpinCandidateMeasurableFundamentalDomain
        V.existsUnique_rationalDiagonal_smul_mem_measurableFundamentalDomain
  simpa only [translated] using htranslatedEq.trans horiginalEq.symm

end CliffordSpinCandidateRawOnoTamagawaData

end RationalQuadraticSpaceMatrix
