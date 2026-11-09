import SMSFormula.QuadraticPadicSquareBranchFiberLocality

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

def padicSquareBranchFiberDomain (form : QuadraticForm ℚ_[prime] space) (point : space) (value : ℚ_[prime]) :
    Set (form.anisotropicOrthogonal point) :=
  (fun transverse ↦ (value - form.orthogonalRestriction point transverse) / form point) ⁻¹'
    Rat.padicUnitSquareScalarTarget prime

omit [MeasurableSpace space] [BorelSpace space] [SecondCountableTopology space] in
theorem isOpen_padicSquareBranchFiberDomain (form : QuadraticForm ℚ_[prime] space) (point : space) (value : ℚ_[prime]) :
    IsOpen (form.padicSquareBranchFiberDomain prime point value) := by
  have hquadratic : Continuous (form.orthogonalRestriction point) := continuous_iff_continuousAt.mpr
    (fun transverse ↦ ((form.orthogonalRestriction point).hasStrictFDerivAt_valueDifferential transverse).continuousAt)
  exact (Rat.isOpen_padicUnitSquareScalarTarget prime).preimage ((continuous_const.sub hquadratic).div_const _)

def padicSquareBranchFiberMap (form : QuadraticForm ℚ_[prime] space) (point : space)
    (hpoint : form point ≠ 0) (value : ℚ_[prime]) :
    form.padicSquareBranchFiberDomain prime point value → {vector : space // form vector = value} :=
  fun transverse ↦ ⟨Rat.padicUnitSquareTargetSupportedInverse prime
    ((value - form.orthogonalRestriction point transverse.val) / form point) • point + transverse.val,
    form.padicSquareBranch_inverse_vector_value prime point hpoint transverse.val value transverse.property⟩

theorem measurable_padicSquareBranchFiberMap (form : QuadraticForm ℚ_[prime] space) (point : space)
    (hpoint : form point ≠ 0) (value : ℚ_[prime]) :
    Measurable (form.padicSquareBranchFiberMap prime point hpoint value) := by
  have hquadratic : Continuous (form.orthogonalRestriction point) := continuous_iff_continuousAt.mpr
    (fun transverse ↦ ((form.orthogonalRestriction point).hasStrictFDerivAt_valueDifferential transverse).continuousAt)
  have hparameter : Measurable (fun transverse : form.padicSquareBranchFiberDomain prime point value ↦
      (value - form.orthogonalRestriction point transverse.val) / form point) :=
    ((continuous_const.sub (hquadratic.comp continuous_subtype_val)).div_const _).measurable
  exact ((((Rat.measurable_padicUnitSquareTargetSupportedInverse prime).comp hparameter).smul measurable_const).add
    (measurable_subtype_coe.comp measurable_subtype_coe)).subtype_mk

def padicSquareBranchFiberJacobianInverse (form : QuadraticForm ℚ_[prime] space) (point : space)
    (value : ℚ_[prime]) (transverse : form.anisotropicOrthogonal point) : ℝ≥0∞ :=
  (‖2 * form point * Rat.padicUnitSquareTargetSupportedInverse prime
    ((value - form.orthogonalRestriction point transverse) / form point)‖₊ : ℝ≥0∞)⁻¹

omit [SecondCountableTopology space] in
theorem measurable_padicSquareBranchFiberJacobianInverse (form : QuadraticForm ℚ_[prime] space)
    (point : space) (value : ℚ_[prime]) :
    Measurable (form.padicSquareBranchFiberJacobianInverse prime point value) := by
  have hquadratic : Continuous (form.orthogonalRestriction point) := continuous_iff_continuousAt.mpr
    (fun transverse ↦ ((form.orthogonalRestriction point).hasStrictFDerivAt_valueDifferential transverse).continuousAt)
  have hparameter : Measurable (fun transverse : form.anisotropicOrthogonal point ↦
      (value - form.orthogonalRestriction point transverse) / form point) :=
    ((continuous_const.sub hquadratic).div_const (form point)).measurable
  exact (measurable_const.mul
    ((Rat.measurable_padicUnitSquareTargetSupportedInverse prime).comp hparameter)).nnnorm.coe_nnreal_ennreal.inv

def padicSquareBranchFiberMeasure (form : QuadraticForm ℚ_[prime] space) (point : space)
    (hpoint : form point ≠ 0) (transverseMeasure : Measure (form.anisotropicOrthogonal point))
    (value : ℚ_[prime]) : Measure {vector : space // form vector = value} :=
  Measure.map (form.padicSquareBranchFiberMap prime point hpoint value)
    ((Measure.comap (Subtype.val : form.padicSquareBranchFiberDomain prime point value → form.anisotropicOrthogonal point)
      transverseMeasure).withDensity
      (fun transverse ↦ form.padicSquareBranchFiberJacobianInverse prime point value transverse.val))

theorem lintegral_padicSquareBranchFiberMeasure (form : QuadraticForm ℚ_[prime] space)
    (point : space) (hpoint : form point ≠ 0)
    (transverseMeasure : Measure (form.anisotropicOrthogonal point)) (value : ℚ_[prime])
    (test : {vector : space // form vector = value} → ℝ≥0∞) (htest : Measurable test) :
    (∫⁻ vector, test vector ∂form.padicSquareBranchFiberMeasure prime point hpoint transverseMeasure value) =
      ∫⁻ transverse : form.padicSquareBranchFiberDomain prime point value,
        form.padicSquareBranchFiberJacobianInverse prime point value transverse.val *
          test (form.padicSquareBranchFiberMap prime point hpoint value transverse)
        ∂Measure.comap Subtype.val transverseMeasure := by
  rw [padicSquareBranchFiberMeasure, lintegral_map htest (form.measurable_padicSquareBranchFiberMap prime point hpoint value)]
  exact lintegral_withDensity_eq_lintegral_mul _
    ((form.measurable_padicSquareBranchFiberJacobianInverse prime point value).comp measurable_subtype_coe)
    (htest.comp (form.measurable_padicSquareBranchFiberMap prime point hpoint value))

theorem lintegral_padicSquareBranchFiberMeasure_restrict_weight (form : QuadraticForm ℚ_[prime] space)
    (point : space) (hpoint : form point ≠ 0)
    (transverseMeasure : Measure (form.anisotropicOrthogonal point)) (value : ℚ_[prime])
    (weight : space → ℝ≥0∞) (hweight : Measurable weight) :
    (∫⁻ vector, weight vector.val ∂form.padicSquareBranchFiberMeasure prime point hpoint transverseMeasure value) =
      form.padicSquareBranchValueDensity prime point transverseMeasure weight value := by
  rw [form.lintegral_padicSquareBranchFiberMeasure prime point hpoint transverseMeasure value
    (fun vector ↦ weight vector.val) (hweight.comp measurable_subtype_coe)]
  change (∫⁻ transverse : form.padicSquareBranchFiberDomain prime point value,
      (fun transverse : form.anisotropicOrthogonal point ↦
        form.padicSquareBranchFiberJacobianInverse prime point value transverse *
          weight (Rat.padicUnitSquareTargetSupportedInverse prime
            ((value - form.orthogonalRestriction point transverse) / form point) • point + transverse)) transverse.val
      ∂Measure.comap Subtype.val transverseMeasure) = _
  rw [lintegral_subtype_comap (μ := transverseMeasure)
    (form.isOpen_padicSquareBranchFiberDomain prime point value).measurableSet
    (fun transverse : form.anisotropicOrthogonal point ↦
      form.padicSquareBranchFiberJacobianInverse prime point value transverse *
        weight (Rat.padicUnitSquareTargetSupportedInverse prime
          ((value - form.orthogonalRestriction point transverse) / form point) • point + transverse))]
  rw [← lintegral_indicator (form.isOpen_padicSquareBranchFiberDomain prime point value).measurableSet]
  apply lintegral_congr
  intro transverse
  classical
  by_cases hmem : transverse ∈ form.padicSquareBranchFiberDomain prime point value
  · unfold padicSquareBranchValueKernel
    rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (show (transverse, value) ∈ _ from hmem)]
    simp only [padicSquareBranchFiberJacobianInverse, div_eq_mul_inv, mul_comm]
  · unfold padicSquareBranchValueKernel
    rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem (show (transverse, value) ∉ _ from hmem)]

end QuadraticMap
