import SMSFormula.QuadraticPadicSquareBranchFiberMeasure

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace QuadraticMap

variable (prime : ℕ) [Fact prime.Prime]

local instance : MeasurableSpace ℚ_[prime] := borel _
local instance : BorelSpace ℚ_[prime] := ⟨rfl⟩

variable {space : Type*} [NormedAddCommGroup space] [NormedSpace ℚ_[prime] space]
  [FiniteDimensional ℚ_[prime] space]

theorem padicSquareBranchFiberMap_coordinates (form : QuadraticForm ℚ_[prime] space)
    (point : space) (hpoint : form point ≠ 0) (value : ℚ_[prime])
    (transverse : form.padicSquareBranchFiberDomain prime point value) :
    (form.anisotropicOrthogonalDecompositionContinuousLinearEquiv point hpoint).symm
      (form.padicSquareBranchFiberMap prime point hpoint value transverse).val =
      (transverse.val, Rat.padicUnitSquareTargetSupportedInverse prime
        ((value - form.orthogonalRestriction point transverse.val) / form point)) := by
  change (form.anisotropicOrthogonalDecompositionContinuousLinearEquiv point hpoint).symm
    (_ • point + transverse.val) = _
  rw [← form.anisotropicOrthogonalDecompositionContinuousLinearEquiv_apply point hpoint
    (transverse.val, Rat.padicUnitSquareTargetSupportedInverse prime
      ((value - form.orthogonalRestriction point transverse.val) / form point))]
  exact (form.anisotropicOrthogonalDecompositionContinuousLinearEquiv point hpoint).symm_apply_apply _

theorem padicSquareBranchFiberMap_injective (form : QuadraticForm ℚ_[prime] space)
    (point : space) (hpoint : form point ≠ 0) (value : ℚ_[prime]) :
    Function.Injective (form.padicSquareBranchFiberMap prime point hpoint value) := by
  intro first second hequal
  have hcoordinates := congrArg (fun vector : {vector : space // form vector = value} ↦
    ((form.anisotropicOrthogonalDecompositionContinuousLinearEquiv point hpoint).symm vector.val).1) hequal
  simp only [form.padicSquareBranchFiberMap_coordinates prime] at hcoordinates
  exact Subtype.ext hcoordinates

theorem range_padicSquareBranchFiberMap (form : QuadraticForm ℚ_[prime] space)
    (point : space) (hpoint : form point ≠ 0) (value : ℚ_[prime]) :
    Set.range (form.padicSquareBranchFiberMap prime point hpoint value) =
      {vector : {vector : space // form vector = value} |
        ((form.anisotropicOrthogonalDecompositionContinuousLinearEquiv point hpoint).symm vector.val).2 ∈
          Rat.padicUnitSquareScalarSource prime} := by
  ext vector
  constructor
  · rintro ⟨transverse, rfl⟩
    change ((form.anisotropicOrthogonalDecompositionContinuousLinearEquiv point hpoint).symm
      (form.padicSquareBranchFiberMap prime point hpoint value transverse).val).2 ∈ Rat.padicUnitSquareScalarSource prime
    rw [form.padicSquareBranchFiberMap_coordinates prime,
      Rat.padicUnitSquareTargetSupportedInverse_eq prime transverse.property]
    exact (Rat.padicUnitSquareScalarInverse_mem_and_sq prime transverse.property).1
  · intro hsource
    let coordinates := (form.anisotropicOrthogonalDecompositionContinuousLinearEquiv point hpoint).symm vector.val
    have hvector : coordinates.2 • point + coordinates.1 = vector.val := by
      rw [← form.anisotropicOrthogonalDecompositionContinuousLinearEquiv_apply point hpoint]
      exact (form.anisotropicOrthogonalDecompositionContinuousLinearEquiv point hpoint).apply_symm_apply _
    have hquadratic : form.orthogonalRestriction point coordinates.1 + coordinates.2 ^ 2 * form point = value := by
      have heq := (form.anisotropicOrthogonalDecompositionIsometryEquiv point hpoint).map_app (coordinates.1, coordinates.2)
      simp only [anisotropicOrthogonalSum, prod_apply, anisotropicScalarLine_apply_eq_sq_mul] at heq
      change form (coordinates.2 • point + coordinates.1) = _ at heq
      rw [hvector, vector.property] at heq
      exact heq.symm
    have hparameter : (value - form.orthogonalRestriction point coordinates.1) / form point = coordinates.2 ^ 2 := by
      rw [← hquadratic, add_sub_cancel_left, mul_div_cancel_right₀ _ hpoint]
    have htarget : coordinates.2 ^ 2 ∈ Rat.padicUnitSquareScalarTarget prime := by
      obtain ⟨unit, hunit, hequal⟩ := hsource
      refine ⟨Rat.unitSquareIdentityChart ℚ_[prime] unit, (Rat.unitSquareIdentityChart ℚ_[prime]).map_source hunit, ?_⟩
      simp only [Rat.unitSquareIdentityChart_apply, Units.val_pow_eq_pow_val, hequal]
      rfl
    have hdomain : coordinates.1 ∈ form.padicSquareBranchFiberDomain prime point value := by
      change (value - form.orthogonalRestriction point coordinates.1) / form point ∈ Rat.padicUnitSquareScalarTarget prime
      rwa [hparameter]
    refine ⟨⟨coordinates.1, hdomain⟩, ?_⟩
    apply Subtype.ext
    change Rat.padicUnitSquareTargetSupportedInverse prime
      ((value - form.orthogonalRestriction point coordinates.1) / form point) • point + coordinates.1 = vector.val
    rw [hparameter, Rat.padicUnitSquareTargetSupportedInverse_eq prime htarget,
      Rat.padicUnitSquareScalarInverse_sq prime hsource]
    exact hvector

theorem continuous_padicSquareBranchFiberMap (form : QuadraticForm ℚ_[prime] space)
    (point : space) (hpoint : form point ≠ 0) (value : ℚ_[prime]) :
    Continuous (form.padicSquareBranchFiberMap prime point hpoint value) := by
  have hquadratic : Continuous (form.orthogonalRestriction point) := continuous_iff_continuousAt.mpr
    (fun transverse ↦ ((form.orthogonalRestriction point).hasStrictFDerivAt_valueDifferential transverse).continuousAt)
  have hparameter : Continuous (fun transverse : form.padicSquareBranchFiberDomain prime point value ↦
      (value - form.orthogonalRestriction point transverse.val) / form point) :=
    (continuous_const.sub (hquadratic.comp continuous_subtype_val)).div_const _
  have hinverse := (Rat.continuousOn_padicUnitSquareScalarInverse prime).comp_continuous hparameter
    (fun transverse ↦ transverse.property)
  have hsupported : Continuous (fun transverse : form.padicSquareBranchFiberDomain prime point value ↦
      Rat.padicUnitSquareTargetSupportedInverse prime ((value - form.orthogonalRestriction point transverse.val) / form point)) := by
    convert hinverse using 1
    funext transverse
    exact Rat.padicUnitSquareTargetSupportedInverse_eq prime transverse.property
  exact ((hsupported.smul continuous_const).add
    (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _

end QuadraticMap
