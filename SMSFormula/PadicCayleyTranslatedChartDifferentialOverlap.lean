import SMSFormula.MeasureMapCommutingSquare
import SMSFormula.PadicCayleyTranslatedChartDifferentialLeft
import SMSFormula.PadicCayleyTranslatedChartDifferentialRight

/-!
# Compatibility of corrected translated p-adic chart differentials

The source-overlap differential restrictions are transported to the common
target from the left and right charts in separate opaque layers.  The
internally proved nonlinear transition invariance then identifies those two
common-target restrictions.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator Topology NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

open Matrix

variable (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)

local instance padicCayleyTranslatedDifferentialOverlapSourceMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance padicCayleyTranslatedDifferentialOverlapSourceBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

local instance padicCayleyTranslatedDifferentialOverlapSubgroupMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℚ_[p]))) :=
  borel _

local instance padicCayleyTranslatedDifferentialOverlapSubgroupBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩

/-- Correctly oriented translated-chart differential measures agree on every
common exact target overlap. -/
theorem
    padicCayleySpecialOrthogonalTranslatedTargetOverlapDifferentialMeasure_eq
    (F : Matrix (Fin n) (Fin n) ℚ) (hFsymm : F.IsSymm)
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    padicCayleySpecialOrthogonalTranslatedTargetOverlapDifferentialMeasureFromLeft
        p n F hF c d =
      padicCayleySpecialOrthogonalTranslatedTargetOverlapDifferentialMeasureFromRight
        p n F hF c d := by
  let μ :=
    skewAdjointPadicCayleyTranslatedSourceOverlapDifferentialMeasure
      p n F hF c d
  let ν :=
    skewAdjointPadicCayleyTranslatedSourceOverlapDifferentialMeasure
      p n F hF d c
  let T :=
    skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
      F p hF c d
  let L :=
    skewAdjointPadicCayleyTranslatedSourceTargetOverlapHomeomorph
      F p hF c d
  let R :=
    skewAdjointPadicCayleyTranslatedSourceTargetOverlapHomeomorphFromRight
      p n F hF c d
  have hT : Measure.map T μ = ν :=
    map_skewAdjointPadicCayleyTranslatedSourceOverlapDifferentialMeasure
      p n F hFsymm hF c d
  have hcommon : Measure.map L μ = Measure.map R ν :=
    Measure.map_eq_map_of_map_eq_of_forall T L R μ ν
      T.measurable R.measurable hT
      (fun X =>
        skewAdjointPadicCayleyTranslatedSourceTargetOverlapHomeomorph_transition
          p n F hF c d X)
  calc
    padicCayleySpecialOrthogonalTranslatedTargetOverlapDifferentialMeasureFromLeft
        p n F hF c d =
      Measure.map L μ :=
      (map_skewAdjointPadicCayleyTranslatedSourceOverlapDifferentialMeasure_left
        p n F hF c d).symm
    _ = Measure.map R ν := hcommon
    _ =
      padicCayleySpecialOrthogonalTranslatedTargetOverlapDifferentialMeasureFromRight
        p n F hF c d :=
      map_skewAdjointPadicCayleyTranslatedSourceOverlapDifferentialMeasure_right
        p n F hF c d

end PositiveDefiniteIntegralLattice
