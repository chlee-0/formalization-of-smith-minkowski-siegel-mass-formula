import SMSFormula.QuadraticPadicSquareBranchSlicing
import SMSFormula.RationalPadicUnitSquareInverseMeasurable

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace QuadraticMap

variable (prime : ℕ) [Fact prime.Prime]

local instance : MeasurableSpace ℚ_[prime] := borel _
local instance : BorelSpace ℚ_[prime] := ⟨rfl⟩

variable {space : Type*} [NormedAddCommGroup space] [NormedSpace ℚ_[prime] space]
  [FiniteDimensional ℚ_[prime] space] [MeasurableSpace space] [BorelSpace space]
  [SecondCountableTopology space]

def padicSquareBranchValueKernel (form : QuadraticForm ℚ_[prime] space) (point : space)
    (weight : space → ℝ≥0∞) : form.anisotropicOrthogonal point × ℚ_[prime] → ℝ≥0∞ :=
  ((fun pair : form.anisotropicOrthogonal point × ℚ_[prime] ↦
      (pair.2 - form.orthogonalRestriction point pair.1) / form point) ⁻¹'
    Rat.padicUnitSquareScalarTarget prime).indicator (fun pair ↦
      weight (Rat.padicUnitSquareTargetSupportedInverse prime
        ((pair.2 - form.orthogonalRestriction point pair.1) / form point) • point + pair.1) /
      (‖2 * form point * Rat.padicUnitSquareTargetSupportedInverse prime
        ((pair.2 - form.orthogonalRestriction point pair.1) / form point)‖₊ : ℝ≥0∞))

theorem measurable_padicSquareBranchValueKernel (form : QuadraticForm ℚ_[prime] space)
    (point : space) (weight : space → ℝ≥0∞) (hweight : Measurable weight) :
    Measurable (form.padicSquareBranchValueKernel prime point weight) := by
  have hquadratic : Continuous (form.orthogonalRestriction point) := continuous_iff_continuousAt.mpr
    (fun transverse ↦ ((form.orthogonalRestriction point).hasStrictFDerivAt_valueDifferential transverse).continuousAt)
  have hparameter : Measurable (fun pair : form.anisotropicOrthogonal point × ℚ_[prime] ↦
      (pair.2 - form.orthogonalRestriction point pair.1) / form point) :=
    ((continuous_snd.sub (hquadratic.comp continuous_fst)).div_const _).measurable
  have hinverse := (Rat.measurable_padicUnitSquareTargetSupportedInverse prime).comp hparameter
  have hvector : Measurable (fun pair : form.anisotropicOrthogonal point × ℚ_[prime] ↦
      Rat.padicUnitSquareTargetSupportedInverse prime
        ((pair.2 - form.orthogonalRestriction point pair.1) / form point) • point + pair.1) :=
    (hinverse.smul measurable_const).add (measurable_subtype_coe.comp measurable_fst)
  exact ((hweight.comp hvector).div
    (measurable_const.mul hinverse).nnnorm.coe_nnreal_ennreal).indicator
    (hparameter (Rat.isOpen_padicUnitSquareScalarTarget prime).measurableSet)

omit [SecondCountableTopology space] [FiniteDimensional ℚ_[prime] space]
  [MeasurableSpace space] [BorelSpace space] in
theorem padicSquareBranchValueKernel_apply (form : QuadraticForm ℚ_[prime] space)
    (point : space) (hpoint : form point ≠ 0) (weight : space → ℝ≥0∞)
    (transverse : form.anisotropicOrthogonal point) (value : ℚ_[prime]) :
    form.padicSquareBranchValueKernel prime point weight (transverse, value) =
      ((fun unit : ℚ_[prime]ˣ ↦ form.orthogonalRestriction point transverse + form point * (unit : ℚ_[prime])) ''
        (Rat.unitSquareIdentityChart ℚ_[prime]).target).indicator
        (fun target ↦ weight (Rat.padicUnitSquareScalarInverse prime
            ((target - form.orthogonalRestriction point transverse) / form point) • point + transverse) /
          (‖2 * form point * Rat.padicUnitSquareScalarInverse prime
            ((target - form.orthogonalRestriction point transverse) / form point)‖₊ : ℝ≥0∞)) value := by
  classical
  have hmembership := Rat.mem_padicUnitSquareScalarAffineTarget_iff prime
    (form.orthogonalRestriction point transverse) (form point) hpoint value
  by_cases hvalue : (value - form.orthogonalRestriction point transverse) / form point ∈
      Rat.padicUnitSquareScalarTarget prime
  · unfold padicSquareBranchValueKernel
    rw [Set.indicator_of_mem (show (transverse, value) ∈ _ from hvalue),
      Set.indicator_of_mem (hmembership.mpr hvalue)]
    dsimp only
    rw [Rat.padicUnitSquareTargetSupportedInverse_eq prime hvalue]
  · unfold padicSquareBranchValueKernel
    rw [Set.indicator_of_notMem (show (transverse, value) ∉ _ from hvalue),
      Set.indicator_of_notMem (hmembership.not.mpr hvalue)]

variable [LocallyCompactSpace space]

theorem lintegral_padicSquareBranch_valueMeasure_kernel
    (form : QuadraticForm ℚ_[prime] space) (point : space) (hpoint : form point ≠ 0)
    (transverseHaar : Measure (form.anisotropicOrthogonal point))
    (scalarHaar : Measure ℚ_[prime]) (vectorHaar : Measure space)
    [transverseHaar.IsAddHaarMeasure] [scalarHaar.IsAddHaarMeasure] [vectorHaar.IsAddHaarMeasure]
    (weight : space → ℝ≥0∞) (hweight : Measurable weight)
    (test : ℚ_[prime] → ℝ≥0∞) (htest : Measurable test) :
    (form.anisotropicOrthogonalProductHaarScalar point hpoint transverseHaar scalarHaar vectorHaar : ℝ≥0∞) *
      (∫⁻ value, test value ∂Measure.map form
        (vectorHaar.withDensity (form.padicSquareBranchWeight prime point hpoint weight))) =
      ∫⁻ value, (∫⁻ transverse, form.padicSquareBranchValueKernel prime point weight (transverse, value)
        ∂transverseHaar) * test value ∂scalarHaar := by
  letI : LocallyCompactSpace (form.anisotropicOrthogonal point) :=
    (form.anisotropicOrthogonal point).closed_of_finiteDimensional.isClosedEmbedding_subtypeVal.locallyCompactSpace
  rw [form.lintegral_padicSquareBranch_valueMeasure prime point hpoint transverseHaar scalarHaar vectorHaar
    weight hweight test htest]
  have hkernel := form.measurable_padicSquareBranchValueKernel prime point weight hweight
  calc
    _ = ∫⁻ transverse, ∫⁻ value,
        form.padicSquareBranchValueKernel prime point weight (transverse, value) * test value
        ∂scalarHaar ∂transverseHaar := by
      apply lintegral_congr
      intro transverse
      simp_rw [form.padicSquareBranchValueKernel_apply prime point hpoint,
        ← Set.indicator_mul_left]
      rw [lintegral_indicator (Rat.isOpen_padicUnitSquareScalarAffineTarget prime
        (form.orthogonalRestriction point transverse) (form point) hpoint).measurableSet]
      apply lintegral_congr
      intro value
      simp only [div_eq_mul_inv, mul_right_comm]
    _ = ∫⁻ value, ∫⁻ transverse,
        form.padicSquareBranchValueKernel prime point weight (transverse, value) * test value
        ∂transverseHaar ∂scalarHaar :=
      lintegral_lintegral_swap ((hkernel.mul (htest.comp measurable_snd)).aemeasurable)
    _ = _ := by
      apply lintegral_congr
      intro value
      exact lintegral_mul_const _ (hkernel.comp (measurable_id.prodMk measurable_const))

def padicSquareBranchValueDensity (form : QuadraticForm ℚ_[prime] space) (point : space)
    (transverseHaar : Measure (form.anisotropicOrthogonal point)) (weight : space → ℝ≥0∞)
    (value : ℚ_[prime]) : ℝ≥0∞ :=
  ∫⁻ transverse, form.padicSquareBranchValueKernel prime point weight (transverse, value) ∂transverseHaar

theorem measurable_padicSquareBranchValueDensity (form : QuadraticForm ℚ_[prime] space)
    (point : space) (transverseHaar : Measure (form.anisotropicOrthogonal point))
    [transverseHaar.IsAddHaarMeasure] (weight : space → ℝ≥0∞) (hweight : Measurable weight) :
    Measurable (form.padicSquareBranchValueDensity prime point transverseHaar weight) := by
  letI : LocallyCompactSpace (form.anisotropicOrthogonal point) :=
    (form.anisotropicOrthogonal point).closed_of_finiteDimensional.isClosedEmbedding_subtypeVal.locallyCompactSpace
  exact (form.measurable_padicSquareBranchValueKernel prime point weight hweight).lintegral_prod_left'

theorem map_padicSquareBranch_withDensity
    (form : QuadraticForm ℚ_[prime] space) (point : space) (hpoint : form point ≠ 0)
    (transverseHaar : Measure (form.anisotropicOrthogonal point))
    (scalarHaar : Measure ℚ_[prime]) (vectorHaar : Measure space)
    [transverseHaar.IsAddHaarMeasure] [scalarHaar.IsAddHaarMeasure] [vectorHaar.IsAddHaarMeasure]
    (weight : space → ℝ≥0∞) (hweight : Measurable weight) :
    (form.anisotropicOrthogonalProductHaarScalar point hpoint transverseHaar scalarHaar vectorHaar : ℝ≥0∞) •
      Measure.map form (vectorHaar.withDensity (form.padicSquareBranchWeight prime point hpoint weight)) =
      scalarHaar.withDensity (form.padicSquareBranchValueDensity prime point transverseHaar weight) := by
  apply Measure.ext_of_lintegral
  intro test htest
  rw [lintegral_smul_measure, lintegral_withDensity_eq_lintegral_mul _
    (form.measurable_padicSquareBranchValueDensity prime point transverseHaar weight hweight) htest]
  exact form.lintegral_padicSquareBranch_valueMeasure_kernel prime point hpoint
    transverseHaar scalarHaar vectorHaar weight hweight test htest

end QuadraticMap
