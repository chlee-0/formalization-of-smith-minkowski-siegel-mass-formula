import SMSFormula.PadicCayleyTranslatedChartRecovery
import Mathlib.MeasureTheory.Measure.Regular

/-!
# Local finiteness of corrected p-adic translated-chart differentials

The corrected Cayley differential density is the reciprocal of the
positive `NNReal` Cayley scalar.  On the exact open Cayley source this
reciprocal is a continuous `NNReal` function.  Weighting the locally finite
source coordinate measure by its coercion therefore remains locally finite.
The translated Cayley homeomorphism transports this property to every exact
translated-target differential measure.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator Topology NNReal ENNReal

namespace Matrix

variable (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)

local instance padicCayleyDifferentialRegularitySourceMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance padicCayleyDifferentialRegularitySourceBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

/-- The corrected differential density on the exact Cayley source, as an
`NNReal` reciprocal before coercion to `ENNReal`. -/
def skewAdjointPadicCayleySourceDifferentialDensityNNReal
    (F : Matrix (Fin n) (Fin n) ℚ)
    (X : skewAdjointPadicCayleySource F p) :
    NNReal :=
  (skewAdjointPadicCayleyCoordinateJacobianDensity p n F X.1)⁻¹

/-- The corrected `NNReal` Cayley source density is continuous. -/
theorem continuous_skewAdjointPadicCayleySourceDifferentialDensityNNReal
    (F : Matrix (Fin n) (Fin n) ℚ) :
    Continuous
      (skewAdjointPadicCayleySourceDifferentialDensityNNReal p n F) := by
  exact
    ((continuous_skewAdjointPadicCayleyCoordinateJacobianDensity
      p n F).comp continuous_subtype_val).inv₀
      (fun X => (skewAdjointPadicCayleyCoordinateJacobianDensity_pos
        p n F X.1 X.2).ne')

/-- The corrected `ENNReal` source density is literally the coercion of its
continuous `NNReal` reciprocal. -/
theorem skewAdjointPadicCayleySourceDifferentialDensityENNReal_eq_coe
    (F : Matrix (Fin n) (Fin n) ℚ)
    (X : skewAdjointPadicCayleySource F p) :
    skewAdjointPadicCayleySourceDifferentialDensityENNReal p n F X =
      (skewAdjointPadicCayleySourceDifferentialDensityNNReal
        p n F X : ENNReal) := by
  exact (ENNReal.coe_inv
    (skewAdjointPadicCayleyCoordinateJacobianDensity_pos
      p n F X.1 X.2).ne').symm

/-- The correctly oriented differential measure on the exact Cayley source
is locally finite. -/
theorem
    skewAdjointPadicCayleySourceDifferentialSubtypeMeasure_isLocallyFinite
    (F : Matrix (Fin n) (Fin n) ℚ) :
    IsLocallyFiniteMeasure
      (skewAdjointPadicCayleySourceDifferentialSubtypeMeasure p n F) := by
  let μ := skewAdjointPadicCayleySourceCoordinateSubtypeMeasure p n F
  letI : IsLocallyFiniteMeasure μ :=
    skewAdjointPadicCayleySourceCoordinateSubtypeMeasure_isLocallyFinite
      p n F
  change IsLocallyFiniteMeasure
    (μ.withDensity
      (skewAdjointPadicCayleySourceDifferentialDensityENNReal p n F))
  have hdensity :
      skewAdjointPadicCayleySourceDifferentialDensityENNReal p n F =
        fun X =>
          (skewAdjointPadicCayleySourceDifferentialDensityNNReal
            p n F X : ENNReal) := by
    funext X
    exact
      skewAdjointPadicCayleySourceDifferentialDensityENNReal_eq_coe
        p n F X
  rw [hdensity]
  exact IsLocallyFiniteMeasure.withDensity_coe
    (continuous_skewAdjointPadicCayleySourceDifferentialDensityNNReal
      p n F)

end Matrix

namespace PositiveDefiniteIntegralLattice

open Matrix

variable (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)

local instance padicCayleyTranslatedDifferentialRegularitySourceMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance padicCayleyTranslatedDifferentialRegularitySourceBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

local instance padicCayleyTranslatedDifferentialRegularityGroupMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℚ_[p]))) :=
  borel _

local instance padicCayleyTranslatedDifferentialRegularityGroupBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩

private theorem isLocallyFiniteMeasure_map_homeomorph
    {α β : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
    [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]
    (e : α ≃ₜ β) (μ : Measure α) [IsLocallyFiniteMeasure μ] :
    IsLocallyFiniteMeasure (Measure.map e μ) := by
  refine ⟨fun y ↦ ?_⟩
  rcases μ.exists_isOpen_measure_lt_top (e.symm y) with
    ⟨U, hyU, hU, hμU⟩
  refine ⟨e.symm ⁻¹' U,
    (hU.preimage e.symm.continuous).mem_nhds hyU, ?_⟩
  rw [Measure.map_apply e.measurable
    (hU.preimage e.symm.continuous).measurableSet]
  have hpreimage : e ⁻¹' (e.symm ⁻¹' U) = U := by
    ext x
    simp
  rw [hpreimage]
  exact hμU

/-- The corrected differential measure on every exact translated Cayley
target is locally finite. -/
theorem
    padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure_isLocallyFinite
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    IsLocallyFiniteMeasure
      (padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure
        p n F hF c) := by
  let μ :=
    Matrix.skewAdjointPadicCayleySourceDifferentialSubtypeMeasure p n F
  let e :=
    skewAdjointPadicCayleyTranslatedHomeomorph F p hF c
  letI : IsLocallyFiniteMeasure μ :=
    Matrix.skewAdjointPadicCayleySourceDifferentialSubtypeMeasure_isLocallyFinite
      p n F
  rw [padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure]
  exact isLocallyFiniteMeasure_map_homeomorph e μ

end PositiveDefiniteIntegralLattice
