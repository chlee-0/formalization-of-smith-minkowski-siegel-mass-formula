import SMSFormula.PadicCayleyHomeomorph
import SMSFormula.PadicCayleyCoordinateJacobianDensityENNRealPositive
import SMSFormula.PadicCayleyDomainOpenness
import Mathlib.MeasureTheory.Measure.Regular
import SMSFormula.PadicCayleyIdentityDifferential
import Mathlib.MeasureTheory.Measure.Support

/-!
# Full support of the p-adic Cayley chart measures

The additive Haar coordinate measure is first comapped to the exact Cayley
source subtype. It is positive on nonempty open sets and absolutely continuous
with respect to the weighted source-subtype density measure. Consequently the
weighted source measure is positive on nonempty opens. The Cayley homeomorphism
transports this property to the exact target subtype, giving full support,
positive total mass, and nonzero source and target chart measures.

This file does not extend the measure to the full special-orthogonal carrier,
prove group invariance, or glue charts.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

namespace Matrix

variable (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)

local instance padicCayleyChartFullSupportSourceMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance padicCayleyChartFullSupportSourceBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

local instance padicCayleyChartFullSupportGroupMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (specialOrthogonalMatrixSet (F.map (algebraMap ℚ ℚ_[p]))) :=
  borel _

local instance padicCayleyChartFullSupportGroupBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (specialOrthogonalMatrixSet (F.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩

/-- The normalized additive coordinate measure, transported to the exact
Cayley source subtype along its canonical inclusion. -/
def skewAdjointPadicCayleySourceCoordinateSubtypeMeasure
    (F : Matrix (Fin n) (Fin n) ℚ) :
    Measure (skewAdjointPadicCayleySource F p) :=
  Measure.comap Subtype.val (skewAdjointPadicCoordinateMeasure F p)

/-- Pushing the source-subtype coordinate measure through its inclusion gives
the ambient coordinate measure restricted to the Cayley source. -/
theorem map_skewAdjointPadicCayleySourceCoordinateSubtypeMeasure
    (F : Matrix (Fin n) (Fin n) ℚ) :
    Measure.map Subtype.val
        (skewAdjointPadicCayleySourceCoordinateSubtypeMeasure p n F) =
      (skewAdjointPadicCoordinateMeasure F p).restrict
        (skewAdjointPadicCayleySource F p) := by
  rw [skewAdjointPadicCayleySourceCoordinateSubtypeMeasure]
  exact map_comap_subtype_coe
    (isOpen_skewAdjointPadicCayleySource F p).measurableSet _

/-- The exact source-subtype coordinate measure is positive on every nonempty
open set. -/
theorem
    skewAdjointPadicCayleySourceCoordinateSubtypeMeasure_isOpenPosMeasure
    (F : Matrix (Fin n) (Fin n) ℚ) :
    Measure.IsOpenPosMeasure
      (skewAdjointPadicCayleySourceCoordinateSubtypeMeasure p n F) := by
  let μ := skewAdjointPadicCoordinateMeasure F p
  letI : Measure.IsAddHaarMeasure μ :=
    skewAdjointPadicCoordinateMeasure_isAddHaarMeasure F p
  rw [skewAdjointPadicCayleySourceCoordinateSubtypeMeasure]
  exact Measure.IsOpenPosMeasure.comap μ
    (isOpen_skewAdjointPadicCayleySource F p).isOpenEmbedding_subtypeVal

end Matrix
