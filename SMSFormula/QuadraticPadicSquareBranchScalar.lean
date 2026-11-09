import SMSFormula.QuadraticPadicSquareBranchFiberMeasure
import SMSFormula.QuadraticScalarOrthogonalTransport

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace QuadraticMap

variable (prime : ℕ) [Fact prime.Prime]

local instance padicSquareBranchScalarMeasurableSpace : MeasurableSpace ℚ_[prime] := borel _
local instance padicSquareBranchScalarBorelSpace : BorelSpace ℚ_[prime] := ⟨rfl⟩

variable {space : Type*} [NormedAddCommGroup space] [NormedSpace ℚ_[prime] space]
  [FiniteDimensional ℚ_[prime] space] [MeasurableSpace space] [BorelSpace space]
  [SecondCountableTopology space]

omit [MeasurableSpace space] [BorelSpace space] [SecondCountableTopology space] in
theorem padicSquareBranchInverse_scalar (form : QuadraticForm ℚ_[prime] space)
    (point : space) (scalar : ℚ_[prime]) (hscalar : scalar ≠ 0)
    (transverse : form.anisotropicOrthogonal point) (value : ℚ_[prime]) :
    Rat.padicUnitSquareTargetSupportedInverse prime
      ((scalar ^ 2 * value - form.orthogonalRestriction (scalar • point)
        (form.scalarOrthogonalContinuousLinearEquiv point scalar hscalar transverse)) / form (scalar • point)) =
      Rat.padicUnitSquareTargetSupportedInverse prime ((value - form.orthogonalRestriction point transverse) / form point) := by
  rw [form.scalarSquareBranchParameter point scalar hscalar transverse value]

omit [MeasurableSpace space] [BorelSpace space] [SecondCountableTopology space] in
theorem padicSquareBranchDomain_scalar_iff (form : QuadraticForm ℚ_[prime] space)
    (point : space) (scalar : ℚ_[prime]) (hscalar : scalar ≠ 0)
    (transverse : form.anisotropicOrthogonal point) (value : ℚ_[prime]) :
    form.scalarOrthogonalContinuousLinearEquiv point scalar hscalar transverse ∈
      form.padicSquareBranchFiberDomain prime (scalar • point) (scalar ^ 2 * value) ↔
    transverse ∈ form.padicSquareBranchFiberDomain prime point value := by
  simp only [padicSquareBranchFiberDomain, Set.mem_preimage]
  rw [form.scalarSquareBranchParameter point scalar hscalar transverse value]

def padicSquareBranchDomainScalarMap (form : QuadraticForm ℚ_[prime] space)
    (point : space) (scalar : ℚ_[prime]) (hscalar : scalar ≠ 0) (value : ℚ_[prime]) :
    form.padicSquareBranchFiberDomain prime point value →
      form.padicSquareBranchFiberDomain prime (scalar • point) (scalar ^ 2 * value) :=
  fun transverse ↦ ⟨form.scalarOrthogonalContinuousLinearEquiv point scalar hscalar transverse.val,
    (form.padicSquareBranchDomain_scalar_iff prime point scalar hscalar transverse.val value).mpr transverse.property⟩

omit [MeasurableSpace space] [BorelSpace space] [SecondCountableTopology space] in
theorem padicSquareBranchFiberMap_scalar (form : QuadraticForm ℚ_[prime] space)
    (point : space) (hpoint : form point ≠ 0) (scalar : ℚ_[prime]) (hscalar : scalar ≠ 0)
    (value : ℚ_[prime]) (transverse : form.padicSquareBranchFiberDomain prime point value) :
    form.padicSquareBranchFiberMap prime (scalar • point)
      (form.quadratic_smul_ne_zero point hpoint scalar hscalar) (scalar ^ 2 * value)
      (form.padicSquareBranchDomainScalarMap prime point scalar hscalar value transverse) =
    form.scalarValueFiberMap scalar value (form.padicSquareBranchFiberMap prime point hpoint value transverse) := by
  apply Subtype.ext
  change Rat.padicUnitSquareTargetSupportedInverse prime
    ((scalar ^ 2 * value - form.orthogonalRestriction (scalar • point)
      (form.scalarOrthogonalContinuousLinearEquiv point scalar hscalar transverse.val)) /
        form (scalar • point)) • (scalar • point) +
      (form.scalarOrthogonalContinuousLinearEquiv point scalar hscalar transverse.val : space) =
    scalar • (Rat.padicUnitSquareTargetSupportedInverse prime
      ((value - form.orthogonalRestriction point transverse.val) / form point) • point + transverse.val)
  rw [form.padicSquareBranchInverse_scalar prime, form.coe_scalarOrthogonalContinuousLinearEquiv, smul_add]
  rw [smul_comm _ scalar point]

omit [MeasurableSpace space] [BorelSpace space] [SecondCountableTopology space] in
theorem padicSquareBranchJacobian_scalar (form : QuadraticForm ℚ_[prime] space)
    (point : space) (scalar : ℚ_[prime]) (hscalar : scalar ≠ 0)
    (transverse : form.anisotropicOrthogonal point) (value : ℚ_[prime]) :
    (‖2 * form (scalar • point) * Rat.padicUnitSquareTargetSupportedInverse prime
      ((scalar ^ 2 * value - form.orthogonalRestriction (scalar • point)
        (form.scalarOrthogonalContinuousLinearEquiv point scalar hscalar transverse)) / form (scalar • point))‖₊ : ℝ≥0∞) =
    (‖scalar ^ 2‖₊ : ℝ≥0∞) *
      (‖2 * form point * Rat.padicUnitSquareTargetSupportedInverse prime
        ((value - form.orthogonalRestriction point transverse) / form point)‖₊ : ℝ≥0∞) := by
  rw [form.padicSquareBranchInverse_scalar prime]
  have halgebra : 2 * form (scalar • point) *
      Rat.padicUnitSquareTargetSupportedInverse prime ((value - form.orthogonalRestriction point transverse) / form point) =
      scalar ^ 2 * (2 * form point *
        Rat.padicUnitSquareTargetSupportedInverse prime ((value - form.orthogonalRestriction point transverse) / form point)) := by
    rw [QuadraticMap.map_smul]
    simp only [smul_eq_mul]
    ring
  rw [halgebra, nnnorm_mul, ENNReal.coe_mul]

omit [MeasurableSpace space] [BorelSpace space] [SecondCountableTopology space] in
theorem padicSquareBranchFiberJacobianInverse_scalar (form : QuadraticForm ℚ_[prime] space)
    (point : space) (scalar : ℚ_[prime]) (hscalar : scalar ≠ 0)
    (transverse : form.anisotropicOrthogonal point) (value : ℚ_[prime]) :
    form.padicSquareBranchFiberJacobianInverse prime (scalar • point) (scalar ^ 2 * value)
      (form.scalarOrthogonalContinuousLinearEquiv point scalar hscalar transverse) =
    ((‖scalar ^ 2‖₊ : ℝ≥0∞))⁻¹ * form.padicSquareBranchFiberJacobianInverse prime point value transverse := by
  unfold padicSquareBranchFiberJacobianInverse
  rw [form.padicSquareBranchJacobian_scalar prime]
  exact ENNReal.mul_inv (Or.inr ENNReal.coe_ne_top)
    (Or.inl ENNReal.coe_ne_top)

omit [MeasurableSpace space] [BorelSpace space] [SecondCountableTopology space] in
theorem padicSquareBranchValueKernel_scalar (form : QuadraticForm ℚ_[prime] space)
    (point : space) (scalar : ℚ_[prime]) (hscalar : scalar ≠ 0)
    (weight : space → ℝ≥0∞) (transverse : form.anisotropicOrthogonal point) (value : ℚ_[prime]) :
    form.padicSquareBranchValueKernel prime (scalar • point) weight
      (form.scalarOrthogonalContinuousLinearEquiv point scalar hscalar transverse, scalar ^ 2 * value) =
    (‖scalar ^ 2‖₊ : ℝ≥0∞)⁻¹ *
      form.padicSquareBranchValueKernel prime point (fun vector ↦ weight (scalar • vector)) (transverse, value) := by
  classical
  have hJacobian := form.padicSquareBranchJacobian_scalar prime point scalar hscalar transverse value
  rw [form.scalarSquareBranchParameter point scalar hscalar transverse value] at hJacobian
  simp only [padicSquareBranchValueKernel, Set.indicator, Set.mem_preimage]
  rw [form.scalarSquareBranchParameter point scalar hscalar transverse value]
  split_ifs
  · rw [form.coe_scalarOrthogonalContinuousLinearEquiv, hJacobian]
    have hvector : Rat.padicUnitSquareTargetSupportedInverse prime
        ((value - form.orthogonalRestriction point transverse) / form point) • (scalar • point) +
        scalar • (transverse : space) =
        scalar • (Rat.padicUnitSquareTargetSupportedInverse prime
          ((value - form.orthogonalRestriction point transverse) / form point) • point + transverse) := by
      rw [smul_add, smul_comm _ scalar point]
    rw [hvector]
    simp only [div_eq_mul_inv]
    rw [ENNReal.mul_inv (Or.inr ENNReal.coe_ne_top) (Or.inl ENNReal.coe_ne_top)]
    exact mul_left_comm _ _ _
  · simp

theorem padicSquareBranchValueDensity_scalar (form : QuadraticForm ℚ_[prime] space)
    (point : space) (scalar : ℚ_[prime]) (hscalar : scalar ≠ 0)
    (transverseMeasure : Measure (form.anisotropicOrthogonal point))
    (weight : space → ℝ≥0∞) (hweight : Measurable weight) (value : ℚ_[prime]) :
    form.padicSquareBranchValueDensity prime (scalar • point)
      (Measure.map (form.scalarOrthogonalContinuousLinearEquiv point scalar hscalar) transverseMeasure)
      weight (scalar ^ 2 * value) =
    (‖scalar ^ 2‖₊ : ℝ≥0∞)⁻¹ * form.padicSquareBranchValueDensity prime point transverseMeasure
      (fun vector ↦ weight (scalar • vector)) value := by
  rw [padicSquareBranchValueDensity, lintegral_map (f := fun transverse ↦
    form.padicSquareBranchValueKernel prime (scalar • point) weight (transverse, scalar ^ 2 * value))
    ((form.measurable_padicSquareBranchValueKernel prime (scalar • point) weight hweight).comp
      (measurable_id.prodMk measurable_const))
    (form.scalarOrthogonalContinuousLinearEquiv point scalar hscalar).continuous.measurable]
  simp_rw [form.padicSquareBranchValueKernel_scalar prime point scalar hscalar weight]
  exact lintegral_const_mul _ ((form.measurable_padicSquareBranchValueKernel prime point
    (fun vector ↦ weight (scalar • vector)) (hweight.comp (continuous_const.smul continuous_id).measurable)).comp
      (measurable_id.prodMk measurable_const))

end QuadraticMap
