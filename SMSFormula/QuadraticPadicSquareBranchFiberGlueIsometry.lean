import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import SMSFormula.QuadraticPadicSquareBranchHaarIndependence
import SMSFormula.QuadraticPadicSquareBranchFiberPositive

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace QuadraticMap

variable (prime : ℕ) [Fact prime.Prime]

local instance padicFiberGlueIsometryMeasurableSpace : MeasurableSpace ℚ_[prime] := borel _
local instance padicFiberGlueIsometryBorelSpace : BorelSpace ℚ_[prime] := ⟨rfl⟩

variable {space : Type*} [NormedAddCommGroup space] [NormedSpace ℚ_[prime] space]
  [FiniteDimensional ℚ_[prime] space]

theorem padicSquareBranchFiberMap_preimage_range_isometry
    (form : QuadraticForm ℚ_[prime] space) (isometry : form.IsometryEquiv form)
    (point : space) (hpoint : form point ≠ 0) (value : ℚ_[prime]) :
    (isometry.valueFiberMap form value) ⁻¹'
      Set.range (form.padicSquareBranchFiberMap prime (isometry point)
        (by simpa only [isometry.map_app] using hpoint) value) =
    Set.range (form.padicSquareBranchFiberMap prime point hpoint value) := by
  rw [form.range_padicSquareBranchFiberMap prime (isometry point)
    (by simpa only [isometry.map_app] using hpoint) value,
    form.range_padicSquareBranchFiberMap prime point hpoint value]
  ext vector
  change ((form.anisotropicOrthogonalDecompositionContinuousLinearEquiv (isometry point)
      (by simpa only [isometry.map_app] using hpoint)).symm (isometry vector.val)).2 ∈
    Rat.padicUnitSquareScalarSource prime ↔ _
  rw [isometry.anisotropicOrthogonalCoordinates_transport form point hpoint vector.val]
  rfl

variable [MeasurableSpace space] [BorelSpace space] [SecondCountableTopology space]
  [LocallyCompactSpace space]

end QuadraticMap
