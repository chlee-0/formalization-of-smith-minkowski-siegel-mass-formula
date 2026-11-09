import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import SMSFormula.QuadraticPadicSquareBranchHaarIndependence
import SMSFormula.QuadraticPadicSquareBranchFiberPositive
import SMSFormula.QuadraticPadicCoordinateBranchScalar

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace QuadraticMap

variable (prime : ℕ) [Fact prime.Prime]

local instance padicFiberGlueScalarMeasurableSpace : MeasurableSpace ℚ_[prime] := borel _
local instance padicFiberGlueScalarBorelSpace : BorelSpace ℚ_[prime] := ⟨rfl⟩

variable {space : Type*} [NormedAddCommGroup space] [NormedSpace ℚ_[prime] space]
  [FiniteDimensional ℚ_[prime] space]

theorem padicSquareBranchFiberMap_preimage_range_scalar
    (form : QuadraticForm ℚ_[prime] space) (point : space) (hpoint : form point ≠ 0)
    (scalar : ℚ_[prime]) (hscalar : scalar ≠ 0) (value : ℚ_[prime]) :
    (form.scalarValueFiberMap scalar value) ⁻¹'
      Set.range (form.padicSquareBranchFiberMap prime (scalar • point)
        (form.quadratic_smul_ne_zero point hpoint scalar hscalar) (scalar ^ 2 * value)) =
    Set.range (form.padicSquareBranchFiberMap prime point hpoint value) := by
  rw [form.range_padicSquareBranchFiberMap prime (scalar • point)
    (form.quadratic_smul_ne_zero point hpoint scalar hscalar) (scalar ^ 2 * value),
    form.range_padicSquareBranchFiberMap prime point hpoint value]
  ext vector
  change ((form.anisotropicOrthogonalDecompositionContinuousLinearEquiv (scalar • point)
      (form.quadratic_smul_ne_zero point hpoint scalar hscalar)).symm (scalar • vector.val)).2 ∈
    Rat.padicUnitSquareScalarSource prime ↔ _
  rw [form.anisotropicOrthogonalCoordinates_scalar point hpoint scalar hscalar vector.val]
  rfl

variable {rank : ℕ}

end QuadraticMap
