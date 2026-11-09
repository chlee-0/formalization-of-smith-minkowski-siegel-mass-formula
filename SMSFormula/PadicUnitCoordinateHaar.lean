import SMSFormula.SkewAdjointPadicMeasure
import Mathlib.Topology.MetricSpace.Ultra.Pi

/-!
# Unit-cube Haar measure on p-adic coordinate spaces

The Haar measure on `κ → ℚ_p` with mass one on the unit cube `ℤ_p^κ`
(the sup-norm closed unit ball). It is characterized by that mass, is invariant
under coordinate permutations, and is the pushforward of the repository's
skew-adjoint coordinate measure under the basis coordinates. These are
identifications of existing normalizations, not new Haar choices.
-/

noncomputable section

open MeasureTheory Metric
open scoped ENNReal

namespace Padic

variable (p : ℕ) [Fact (Nat.Prime p)]

local instance unitHaarMeasurableSpace : MeasurableSpace ℚ_[p] := borel _
local instance unitHaarBorelSpace : BorelSpace ℚ_[p] := ⟨rfl⟩

variable (κ : Type*) [Fintype κ]

/-- The unit cube `ℤ_p^κ`, as a positive compact set. -/
def unitCube : TopologicalSpace.PositiveCompacts (κ → ℚ_[p]) where
  carrier := closedBall 0 1
  isCompact' := isCompact_closedBall 0 1
  interior_nonempty' := by
    rw [(IsUltrametricDist.isOpen_closedBall (0 : κ → ℚ_[p]) one_ne_zero).interior_eq]
    exact ⟨0, mem_closedBall_self zero_le_one⟩

/-- The Haar measure with mass one on the unit cube. -/
def unitHaar : Measure (κ → ℚ_[p]) := Measure.addHaarMeasure (unitCube p κ)

instance : (unitHaar p κ).IsAddHaarMeasure := by
  unfold unitHaar; infer_instance

theorem unitHaar_unitCube : unitHaar p κ (closedBall 0 1) = 1 :=
  Measure.addHaarMeasure_self

variable {p κ}

/-- A Haar measure with mass one on the unit cube is the unit-cube Haar. -/
theorem eq_unitHaar_of_unitCube (ν : Measure (κ → ℚ_[p])) [ν.IsAddHaarMeasure]
    (h : ν (closedBall 0 1) = 1) : ν = unitHaar p κ := by
  rw [Measure.addHaarMeasure_unique ν (unitCube p κ)]
  change ν (closedBall 0 1) • unitHaar p κ = _
  rw [h, one_smul]

/-- Coordinate permutations preserve the unit-cube Haar measure. -/
theorem map_funCongrLeft_unitHaar {ι : Type*} [Fintype ι] (e : κ ≃ ι) :
    (unitHaar p ι).map (LinearEquiv.funCongrLeft ℚ_[p] ℚ_[p] e).toContinuousLinearEquiv =
      unitHaar p κ := by
  apply eq_unitHaar_of_unitCube
  rw [Measure.map_apply
    (LinearEquiv.funCongrLeft ℚ_[p] ℚ_[p] e).toContinuousLinearEquiv.continuous.measurable
    isClosed_closedBall.measurableSet]
  have hpre : ((LinearEquiv.funCongrLeft ℚ_[p] ℚ_[p] e).toContinuousLinearEquiv :
      (ι → ℚ_[p]) → (κ → ℚ_[p])) ⁻¹' closedBall 0 1 = closedBall 0 1 := by
    ext u
    simp only [Set.mem_preimage, mem_closedBall_zero_iff,
      pi_norm_le_iff_of_nonneg zero_le_one, LinearEquiv.coe_toContinuousLinearEquiv',
      LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
    exact ⟨fun h i ↦ by simpa using h (e.symm i), fun h k ↦ h (e k)⟩
  rw [hpre, unitHaar_unitCube]

end Padic

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]

local instance unitHaarSkewMeasurableSpace :
    MeasurableSpace (skewAdjointMatricesLieSubalgebra (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _
local instance unitHaarSkewBorelSpace :
    BorelSpace (skewAdjointMatricesLieSubalgebra (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩
local instance unitHaarPadicMeasurableSpace : MeasurableSpace ℚ_[p] := borel _
local instance unitHaarPadicBorelSpace : BorelSpace ℚ_[p] := ⟨rfl⟩

/-- The repository's skew-adjoint coordinate measure, read in basis
coordinates, is the unit-cube Haar measure. -/
theorem map_skewAdjointPadicCoordinateMeasure :
    (skewAdjointPadicCoordinateMeasure F p).map (skewAdjointPadicCoordinateEquiv F p) =
      Padic.unitHaar p (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F))) := by
  haveI := skewAdjointPadicCoordinateMeasure_isAddHaarMeasure F p
  apply Padic.eq_unitHaar_of_unitCube
  rw [Measure.map_apply (skewAdjointPadicCoordinateEquiv F p).continuous.measurable
    isClosed_closedBall.measurableSet]
  have hpre : (skewAdjointPadicCoordinateEquiv F p) ⁻¹' closedBall 0 1 =
      (skewAdjointPadicCoordinateLattice F p : Set _) := by
    ext x
    rw [Set.mem_preimage, mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one,
      SetLike.mem_coe, mem_skewAdjointPadicCoordinateLattice_iff]
  rw [hpre]
  exact skewAdjointPadicCoordinateMeasure_lattice F p

end Matrix
